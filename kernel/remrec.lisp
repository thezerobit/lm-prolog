;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


(defun remove-recursions-from-file (from-file-name to-file-name)
  (with-open-file (from from-file-name ':in)
    (with-open-file (to to-file-name ':out)
      (let ((eof (cons nil nil))
            (standard-output to))
        (do ((form (read from eof) (read from eof)))
            ((eq form eof))
          (cond ((and (consp form)
                      (eq (first form) 'defun)
                      (print (remove-recursions-from-defun form))))
                (t (print form))))))))

(defconst *remove-recursions* t
  "If non-nil tail-recursions are turned into iteration")

(defmacro deffun arguments
  "Just like Defun except that tail-recursion optimization is done if *remove-recursions*"
 (cond (*remove-recursions*
        (remove-recursions-from-defun (cons 'defun arguments)))
       (t (cons 'defun arguments))))

(defmacro deffsubst arguments
  "Just like Defsubst except that tail-recursion optimization is done if *remove-recursions*"
  ;;if there are any recursions left this becomes a defun
 (cond (*remove-recursions*
        (remove-recursions-from-defun (cons 'defsubst arguments)))
       (t (cons 'defun arguments))))

(defun contains (form x)
  (cond ((eq x form))
        ((consp form)
         (or (contains (first form) x) (contains (rest1 form) x)))))

(defvar *keep-original-definitions* nil
  "If non-nil then DEFFUN will put the original definition on the property list")

(defun keep-if-need-be (function-name form)
  (cond (*keep-original-definitions*
         `((defprop ,function-name ,form original-definition )))))

(defvar *new-names* () "The variable names to PSETQ in a tail recursive goto.")

;;; Begin changes for version 8.0.

(defun parse-defun (defun)
  (let* ((function-name (cadr defun))
	 (argument-list (ldiff (caddr defun) (memq '&aux (caddr defun))))
	 (body (cdddr defun))
	 declaration-part 
	 (pattern (cons function-name (default-pattern argument-list))))
    (let-if (or (stringp (car body))
		(eq 'declare (careful-first (car body))))
	    ((declaration-part (list (car body))) (body (cdr body)))
      (let-if (eq 'comment (caar body))
	      ((pattern (cons (get (car body) ':predicator) (get (car body) ':argument-list)))
	       (body (cdr body)))
	(values function-name argument-list (memq '&aux (caddr defun))
		declaration-part body pattern
		(mapcan #'(lambda (x)
			    (cond ((not (memq x lambda-list-keywords))
				   (list (careful-first x)))))
			argument-list))))))

(defun default-pattern (args)
  (cond ((eq '&rest (car args)) '(&rest))
	((eq '() (car args)) ())
	((memq (car args) lambda-list-keywords)
	 (default-pattern (cdr args)))
	(t (cons '* (default-pattern (cdr args))))))

(defvar *call-pattern* () "Predicator and argument list declaration of current frob.")

(defun remove-recursions-from-defun (form)
 ;;works by rebinding the lambda-variables and defining a macro which expands
 ;;to a SETQ and GO
  (multiple-value-bind (function-name argument-list AUX-PART
			declaration-part body *CALL-PATTERN* iterative-names)
      (parse-defun form)
    (LET* ((label-name (intern (string-append function-name "-Label")))
	   (defsubst-arguments
	     ;;The idea being to make deffsubst be safe w.r.t. choice of arg. names.
	     (and (eq (first form) 'defsubst)
		  (EQ (FIRST *CALL-PATTERN*) FUNCTION-NAME)	;don't do it for compiled guys
		  (mapcar #'careful-first argument-list)))	;predicates
	   (new-names
	     (new-names-for-arguments
	       iterative-names
	       (and (EQ (FIRST *CALL-PATTERN*) FUNCTION-NAME)	;don't do it for compiled guys
		    (local-variables-in-forms body))))
	   (new-body
	     (body-of-iterative-form function-name label-name new-names iterative-names body
				     defsubst-arguments AUX-PART)))
      (cond ((eq new-body body) ;;nothing could be done
	     `(progn 'compile
		     ,@(keep-if-need-be function-name form)
		     (,(first form)
			,function-name
			,ARGUMENT-LIST
			,@declaration-part
			,@(COND ((CDR AUX-PART) `((LET ,(CDR AUX-PART) ,@BODY)))
				(T BODY)))))
	    ((and (eq (first form) 'defsubst)
		  (contains-recursive-call-p function-name new-body))
	     (remove-recursions-from-defun (cons 'defun (rest1 form))))
	    (t `(progn 'compile
		       ,@(keep-if-need-be function-name form)
		       (,(first form)
			,function-name
			,(defsubst-arglist defsubst-arguments
					   (mapcar #'cons iterative-names new-names)
					   argument-list)
			,@declaration-part
			,@NEW-BODY)))))))

(defun body-of-iterative-form (function-name label-name *new-names* old-names
                               body defsubst-p AUX-PART)
 (let ((bindings
	 (mapcan
	     #'(lambda (new-name OLD-name)
		 (cond ((eq new-name OLD-name) nil)
		       ((not (atom new-name))
			(list (list (first OLD-name)
				    (first new-name))))
		       (t (list (list OLD-name new-name)))))
	     *new-names* OLD-names))
       (new-body (replace-iterative-calls-in-last function-name label-name body)))
   (cond ((eq (last-element new-body) (last-element body))
          body)  ;;no optimizations possible
         (t `((prog ,(and defsubst-p
			  (mapcan
			    #'(lambda (name old)
				(cond ((not (memq name lambda-list-keywords))
				       (list (list name (defsubstify old () defsubst-p))))))
			    *new-names* old-names))
		    ,label-name
		    (return (LET ,(APPEND BINDINGS (CDR AUX-PART)) ,@NEW-BODY))))))))

(DEFSUBST -P (D) (MEMQ D '(- *)))

(DEFSUBST +P (D) (NOT (-P D)))

(defun arg-matcher (list-or-list* CALL-PATTERN formals actuals)
  (cond ((EQ T (CAR CALL-PATTERN))
	 ;;NO CONTINUATION IN A TAIL-RECURSIVE :DETERMINISTIC :ALWAYS DEFFSUBST.
	 (arg-matcher list-or-list* (cdr CALL-PATTERN) FORMALS (cdr actuals)))
	((null formals) ()) ;;should really check actuals too...
        ((and (MEMQ '&REST *CALL-PATTERN*) (null (cdr formals)))
         (list*-if-neq
           (car formals)
           `(,(selectq list-or-list*
                (list 'prolog-list)
                (list* 'prolog-list*))
             ,@actuals)
	   ()
	   T))
        ((and (eq 'list* list-or-list*) (null (cdr actuals)))
         (list* (car formals)
                `(car ,(car actuals))
                (arg-matcher
                  list-or-list*
		  (cdr CALL-PATTERN)
                  (cdr formals)
                  `((cdr ,(car actuals))))))
        (t (list*-if-neq
             (car formals)
             (car actuals)
             (arg-matcher
	       list-or-list* (cdr CALL-PATTERN) (cdr formals) (cdr actuals))
	     (+P (car CALL-PATTERN))))))

(defun list*-if-neq (x y z &optional must-dereference)
  (let ((y (macroexpand
             (cond ((and (consp y) (eq 'list*-in-area (first y)) (null (rest3 y)))
                    (third y))
		   ((and (consp y) (eq 'prolog-list* (first y)) (null (rest2 y)))
                    (second y))
                   (t y)))))
    (cond ((eq x y) z)
	  ((AND MUST-DEREFERENCE
		(not (memq (careful-first y)
			   '(car cdr prolog-cons prolog-list prolog-list*
				 cons-in-area list-in-area list*-in-area))))
	   `(,X (%DEREFERENCE ,Y) ,@Z))
	  (t `(,x ,y ,@z)))))

(defun make-macro-application (list-or-list* label-name arguments)	;8
  (let* ((bindings (arg-matcher list-or-list* (cdr *CALL-PATTERN*) *new-names* arguments)))
    (cond ((null bindings) `(go ,label-name))
          (t `(progn (psetq ,@bindings)
                     (go ,label-name))))))

(defvar *special-forms-that-return-last* '(and or progn let let*))  

(defun replace-iterative-calls-with-macro-2 (function-name label-name form)
 ;;this replaces all tail recursive calls to function-name with label-name
  (cond ((atom form) form)
	(t (let ((function (car form)) (arguments (cdr form)))
             (cond ((eq function function-name)
                    (make-macro-application 'list label-name arguments))
                   ((eq function 'quote) form)
                   ((eq function 'cond)
                    (cons 'cond
                          (mapcar
                            #'(lambda (clause)
                                (cond ((eq clause (car (last arguments)))
                                       (replace-iterative-calls-in-last
                                         function-name label-name clause))
                                      (t (cons (first clause)
                                               (replace-iterative-calls-in-last
                                                 function-name label-name (rest1 clause))))))
                                arguments)))
                   ((memq function *special-forms-that-return-last*)
                    (cons function
                          (replace-iterative-calls-in-last function-name
                                                           label-name
                                                           arguments)))
                   ((eq function 'funcall)
                    (cond ((RECURSIVE-CALL-P arguments)
                           (make-macro-application 'list
                                                   label-name
                                                   (rest1 arguments)))
                          (t form)))
                   ((EQ FUNCTION 'LEXPR-FUNCALL)
                    (cond ((RECURSIVE-CALL-P arguments)
                           (make-macro-application 'list*
                                                   label-name
                                                   (rest1 arguments)))
                          (t form)))
                   ((eq function 'prog)
                    (list* function (first arguments)
                           (mapcar
                             #'(lambda (form)
                                 (replace-iterative-calls-with-macro
                                   (list 'inside-prog function-name)
                                   label-name
                                   form))
                             (rest1 arguments))))
                   ((and (eq function 'return)
                         (consp function-name)
                         (eq (first function-name) 'inside-prog))
                    ;;if its a recursive call in the return then flush the return
                    (cond ((and (consp (first arguments)) (null (rest1 arguments)))
                           (list 'return
                                 (replace-iterative-calls-with-macro
                                   (second function-name)
                                   label-name
                                   (first arguments))))
                          (t form)))
                   ((symbolp function)
                    (let ((expansion (macroexpand form)))
                      (cond ((eq expansion form) ;;didnt expand
                             form)
                            (t (let ((new-form
                                       (replace-iterative-calls-with-macro
                                         function-name
                                         label-name
                                         expansion)))
                                 (cond ((eq new-form expansion)
                                        ;;didnt help to expand it
                                        form)
                                       (t new-form)))))))
                   ((eq (first function) 'lambda)
                    (cons
                      (list* 'lambda
                             (second function)
                             (replace-iterative-calls-in-last
                               function-name
                               label-name
                               (rest2 function)))
                      arguments))
                   (t form))))))

(DEFUN RECURSIVE-CALL-P (FORM)
  (COND ((CONSP (CAR FORM))
	 (SELECTQ (CAAR FORM)
	   ((QUOTE FUNCTION) (EQ (CADAR FORM) (CAR *CALL-PATTERN*)))
	   (CURRENT-ENTRYPOINT
	    (AND (EQUAL (CADAR FORM) `',(CAR *CALL-PATTERN*))
		 #+LEXICAL (TRIVIAL-CONTINUATION-P (CADR FORM))
		 (OR (NEQ T (CADR *CALL-PATTERN*))
		     (EQUAL #-LEXICAL ''(TRUE) #+LEXICAL #'TRUE (MACROEXPAND (CADR FORM))))))))))

;;; End changes for version 8.0.

(defun defsubst-arglist (defsubst-arguments mapping argument-list)
  (cond ((null argument-list) ())
	((memq (car argument-list) lambda-list-keywords)
	 (cons (car argument-list)
	       (defsubst-arglist defsubst-arguments mapping (cdr argument-list))))
	(t (cons (defsubstify (car argument-list) mapping defsubst-arguments)
		 (defsubst-arglist defsubst-arguments mapping (cdr argument-list))))))

(defun defsubstify (x mapping defsubst-arguments)
  (cond ((consp x)
	 (cons (defsubstify (car x) mapping defsubst-arguments)
	       (defsubstify (cdr x) mapping defsubst-arguments)))
	((memq x defsubst-arguments)
	 (intern (string-append x "-defsubst")))
	((assq x mapping) (cdr (assq x mapping)))
	(x)))

(defun new-names-for-arguments (iterative-names local-variables)
 (cond ((null iterative-names) nil)
       (t (let ((name (first iterative-names)))
	    (cons (iterative-variable-name name local-variables)
		  (new-names-for-arguments (rest1 iterative-names)
					   local-variables))))))

(defun local-variables-in-forms (forms)
  (cond ((null forms) nil)
        (t (append (local-variables-in-form (first forms))
                   (local-variables-in-forms (rest1 forms))))))

(defun local-variables-in-form (form)
 ;;this returns all LAMBDA, DO, and PROG variables in form
  (cond ((atom form) nil)
	(t (let ((first (car form)) (rest (cdr form)))
	     (selectq first
	       ((LET LET* DO DO* PROG PROG*)
		;;if there are local variables in the SECOND of the do
		;;then this will not see them
		(cond ((and (eq first 'prog) (first rest) (atom (first rest)))
		       ;;named prog, system-93
		       (append (mapcar #'careful-first (second rest))
			       (local-variables-in-forms (rest2 rest))))
		      (t
		       (append (mapcar #'careful-first (first rest))
			       (local-variables-in-forms (rest1 rest))))))
	       ((DO-NAMED DO*-NAMED)
		(append (mapcar #'careful-first (second rest))
			(local-variables-in-forms (rest2 rest))))
	       ((LAMBDA)
		(append (first rest) ;;this will copy the orginal
			(local-variables-in-forms (rest1 rest))))
	       ((QUOTE COMMENT) nil)
	       (t (let ((new-form (macroexpand form)))
		    (cond ((neq form new-form)
			   (local-variables-in-form new-form))))))))))
  
(defun iterative-variable-name (name local-variables)
  (cond ((not (atom name))
         (let ((first-name
                 (iterative-variable-name (first name) local-variables))
               (second-name
                 (iterative-variable-name (second name) local-variables)))
           (cond ((and (eq (first name) first-name)
                       (eq (second name) second-name))
                  name)
                 (t (list* first-name second-name (rest2 name))))))
        ((memq name local-variables)
        ;;to avoid possible name conflicts must rename the variable 
         (intern (string-append name "-external")))
        (t name)))
   
(defun replace-iterative-calls-with-macro (function-name label-name form)
 ;;this replaces all tail recursive calls to function-name with label-name
 (let ((new-form
         (replace-iterative-calls-with-macro-2 function-name label-name form)))
   (cond ((equal form new-form) form)
         (t new-form))))

(defun replace-iterative-calls-in-last (function-name label-name clauses)
 (cond ((null clauses) clauses)
       ((null (rest1 clauses)) ;;its the last one
        (list
          (replace-iterative-calls-with-macro function-name
                                              label-name
                                              (first clauses))))
       (t (cons (first clauses)
                (replace-iterative-calls-in-last function-name
                                                 label-name
                                                 (rest1 clauses))))))

(defun contains-recursive-call-p (function body)
  ;;this should be a good enough approximation though
  ;;special forms can make this return T when its not recursive
  (contains body function))
