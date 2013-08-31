;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;this file contains a few macros that need to be shared between
;;instead-of-ucode and support in LM-Prolog

(defun make-static-area (&rest args)
  (cond ((memq 'si:volatility (mapcar 'careful-first (arglist 'make-area)))
	 (lexpr-funcall 'make-area ':gc ':dynamic ':volatility 1 args))
	(t (lexpr-funcall 'make-area ':gc ':static args))))

(defun make-temporary-area (&rest args)
  (cond ((memq 'si:volatility (mapcar 'careful-first (arglist 'make-area)))
	 (lexpr-funcall 'make-area ':gc ':dynamic ':volatility 3 args))
	(t (lexpr-funcall 'make-area ':gc ':temporary args))))

;;Some of these have to be reachable from the ucode.
(defvar *vector* nil "The interpreter's non-recursive environment.")

(defvar *trail-array* nil "The current Prolog's reset list.")

(defvar *trail* nil "Direct access variable to active count of current *TRAIL-ARRAY*")

;Used to be one per top level
(defvar *single-prolog-work-area*
	(make-temporary-area
	  ':name '|Work area for LM-Prolog|
	  ':region-size #o200000 ;;1/256 virtual memory
	  ':representation ':list ;;for initial region
	  ))

(defvar *prolog-work-area* *single-prolog-work-area* 
  "The current area for temporary consing in Prolog")

(defvar *universe* ()
  "Definitions of predicates are found by searching this list of worlds")

(defvar *conses-alist* () "Alist used when copying interpreter terms to preserve isomorphy and guarantee termination"
)

(defvar *unsafe-rest-argument* T		;Until there is better support for rest args...
  "T if predicator being defined should copy its rest argument.")


(defvar *variables-shared-between-top-level-stack-groups*
        '(*trail-array* function continuation arglist
	  *prolog-work-area* *cut-tag* *vector* *step* *history* *ancestors*
	  *symbol-table* *definition*
	  *terminal-io* *standard-input* *standard-output* *query-io*
	  #-symbolics *package* ;;I don't know why but otherwise I really break the reader
           ))


#-3600
(defsubst trail (x)
  (or (array-push *trail-array* x) (array-push-extend *trail-array* x)))

#+3600
(defun trail (x)
  (let ((index *trail*)
	(len (array-leader *trail-array* 1)))
    (cond ((>= index len)
	   (adjust-array-size
	     *trail-array*
	     (setf (array-leader *trail-array* 1) (+ len (// len 2))))))
    (aset x *trail-array* index)
    (incf *trail*)
    index))

(defsubst untrail (mark) (%untrail mark))

(defsubst fast-locative-p (x)
  (eq (%data-type x) dtp-locative))

(defsubst value-cell-p (x) (fast-locative-p x))


(deffsubst rest-arg-fixup-loop (rest-arg)
  (cond ((= dtp-locative (%p-data-type rest-arg))
	 (%p-store-data-type rest-arg dtp-external-value-cell-pointer)))
  (SELECT (%P-CDR-CODE REST-ARG)
    (CDR-NEXT (rest-arg-fixup-loop (rest1 rest-arg)))
    (CDR-NORMAL (rest-arg-fixup-loop (%MAKE-POINTER-OFFSET DTP-LIST REST-ARG 1)))))

;(defun rest-arg-copy (rest-arg)
;  (setq rest-arg (copylist rest-arg *prolog-work-area*))
;  (cond ((consp rest-arg) (rest-arg-fixup-loop rest-arg)))
;  rest-arg)

;Courtesy COPYLIST.
(DEFUN rest-arg-copy (LIST)
  (IF (ATOM LIST) LIST
    (LET ((NEWLIST (MAKE-LIST (LENGTH LIST) :AREA *prolog-work-area*)))
      (DO ((L1 LIST (CDR L1))
	   (L2 NEWLIST (CDR L2)))
	  ((ATOM L1))
	(SETF (CAR L2) (CAR L1))
	(cond ((= dtp-locative (%p-data-type l2))
	       (%p-store-data-type l2 dtp-external-value-cell-pointer))))
      NEWLIST)))

(defun rest-arg-fixup (rest-arg)
  (cond ((consp rest-arg) (rest-arg-fixup-loop rest-arg)))
  rest-arg)

#+lexical
(defmacro invoke (x)
  (cond ((and (consp x) (eq 'continuation (car x))) (cadr x))
	(t `(funcall ,x))))

#-lexical
(defmacro invoke (x)
  (cond ((atom x) `(%invoke ,x))
        ((eq 'continuation (car x)) (second x))
        ((eq 'quote (car x)) `(apply ',(car (second x)) ',(cdr (second x))))
        (t `(%invoke ,x))))

;;the following three macros make life easier for the system's consing.
#-(OR 3600 PROLOG-MICRO-CODE)
(progn 'compile
(defmacro prolog-cons (x y)
  `(REST-ARG-FIXUP (cons-in-area ,X ,Y *prolog-work-area*)))

(defmacro prolog-list (&rest elements)
  (COND (ELEMENTS `(REST-ARG-FIXUP (list-in-area *prolog-work-area* ,@ELEMENTS)))))

(defmacro prolog-list* (&rest elements)
  (COND ((CDR ELEMENTS)
	 `(REST-ARG-FIXUP (list*-in-area *prolog-work-area* ,@ELEMENTS)))
	(ELEMENTS (CAR ELEMENTS))
	(T (BREAK "PROLOG-LIST* of 0 arguments."))))

)

#+PROLOG-MICRO-CODE
(progn 'compile
(defmacro prolog-cons (x y)
  `(cons-in-area ,(reference-if-needed x) ,(reference-if-needed y)  *prolog-work-area*))

(defmacro prolog-list (&rest elements)
  `(list-in-area *prolog-work-area* ,@(mapcar #'reference-if-needed elements)))

(defmacro prolog-list* (&rest elements)
  `(list*-in-area *prolog-work-area* ,@(mapcar #'reference-if-needed elements)))

(deffun reference-if-needed (form)			;7.12
  (cond ((consp form)
	 (selectq (car form)
	   (let				   ;common in nested continuations
	    (selectq (car (reference-if-needed (third form)))
	      (%reference `(%reference ,form))
	      (t form)))
	   ((%dereference %reference)
	    (reference-if-needed (cadr form)))
	   ((quote function prolog-cons prolog-list prolog-list* continuation
		   current-entrypoint)
	    form)
	   (t `(%reference ,form))))
	((and (symbolp form) (not (memq form '(nil t .continuation.))))
	 `(%reference ,form))
	(t form))))

(comment
#+3600
(progn 'compile
(defmacro prolog-cons (x y)
  `(cons-in-area ,(reference-if-needed x) ,(reference-if-needed y)  *prolog-work-area*))

(defmacro prolog-list (&rest elements)
  `(prolog-list* ,@elements nil))

(defmacro prolog-list* (&rest elements)
  (turn-into-prolog-cons elements))

(defun turn-into-prolog-cons (elements)
  (cond ((cdr elements)
	 `(prolog-cons ,(car elements) ,(turn-into-prolog-cons (cdr elements))))
	(t (car elements))))))


#+3600
(progn 'compile
(defmacro prolog-list (&rest elements)
  (let ((l (length elements)))
    (cond ((zerop l) `nil)
	  (t `(%prolog-list ,l ,@elements)))))

(defmacro prolog-list* (&rest elements)
  (let ((l (length elements)))
    (cond ((= 1 l) `,(car elements))
	  (t `(%prolog-list* ,l ,@elements))))))

#-3600
(defmacro with-cons-bound-to-cons (x y &body body)
  `(without-interrupts
     (si:%bind (%make-pointer dtp-locative ,x)
	       (%make-pointer dtp-rplacd-forward ,y))
     ,@body))

#+3600
(defmacro with-cons-bound-to-cons (x y &body body)
  `(with-stack-list* (with-cons-bound-to-cons-item ,x ,y)
     (with-stack-list* (*conses-alist* with-cons-bound-to-cons-item *conses-alist*)
       ,@body)))

#-3600
(defmacro with-cons-parts (ignore &body body)
  `(progn . ,body))

#+3600
(defmacro with-cons-parts (x &body body)
  `(let ((with-cons-parts-item (assq ,x *conses-alist*)))
     (let-if with-cons-parts-item ((,x (cdr with-cons-parts-item))) ,@body)))


;;;Here is the beginning of a simple scheme for dispatching on things like
;;;the data-type.

(deffun variables-used (varlist form)
  (cond (varlist
	 (cond ((not (contains form (car varlist)))
		(variables-used (cdr varlist) form))
	       (t (cons (car varlist) (variables-used (cdr varlist) form)))))))

(defmacro define-dispatch-table
	  (macro-name ARGLIST NEW-ARGLIST OFFSET-FORMS &rest make-array-arguments)
  " (DEFINE-DISPATCH-TABLE <macro-name> <ARGLIST> <NEW-ARGLIST> <OFFSET-FORMS> ...)
followed by
 (DEFINE-DISPATCH-ENTRY <macro-name> <integer-name> ...)
will set up a dispatch table such that 
 (<macro-name> <arglist>) applies (AREF . <offset-forms>) to <new-arglist>."
  (let* ((table-name
	   (intern (string-append macro-name "-DISPATCH-TABLE") ':prolog))
	 (unsafe (intersection
		   (variables-used arglist offset-forms)
		   (variables-used arglist new-arglist)))
	 (safe
	   (mapcar #'(lambda (x) (intern (format nil "~a-defsubst" x) ':prolog))
		   unsafe))
	 (sublis-alist (mapcar #'cons unsafe safe)))
    `(progn 'compile
	    (defvar ,table-name (make-array . ,make-array-arguments))
	    (defsubst ,macro-name ,arglist
	      (let ,(mapcar #'list safe unsafe)
		(funcall
		  (aref ,table-name ,@(sublis sublis-alist offset-forms))
		  ,@(sublis sublis-alist new-arglist)))))))

(defmacro define-dispatch-entry (macro-name dispatch-name arglist &body body)
  (let ((entry-name
	  (intern (FORMAT NIL "~A-~A" macro-name dispatch-name) ':prolog)))
    `(progn 'compile
	    (defun ,entry-name ,arglist . ,body)
	    (aset #',entry-name
		  ,(intern (string-append macro-name "-DISPATCH-TABLE") ':prolog)
		  ,dispatch-name))))

(defmacro alter-dispatch-entry (macro-name dispatch-name spec)
  `(aset ,spec
	 ,(intern (string-append macro-name "-DISPATCH-TABLE") ':prolog)
	 ,dispatch-name))

;;A common special case in LM-Prolog is: dispatch on data-type of 1st arg
;; and default with the fastest identity function.
(defmacro define-dtp-table (name arglist &rest options)
  `(define-dispatch-table ,name ,arglist ,arglist
     ((%data-type ,(first arglist)))
     #-3600 32. #+3600 64. ,@options))

(defmacro define-dtp-entry (x y z &body body)
  `(define-dispatch-entry ,x ,y ,z ,@body))

(defmacro alter-dtp-entry (&rest arglist)
  `(alter-dispatch-entry ,@arglist))

;Has to be around when UCODE is fasloaded...
#-3600 #8R COMPILER:
(DEFMACRO PROLOG:DEFMIC (&REST ARGS)
  (LET ((FN (CAR ARGS)))
    `(EVAL-WHEN (#+cadr COMPILE EVAL LOAD)
       (DEFMIC ,@ARGS)
       ,@(COND ((MEMQ '&REST (THIRD ARGS))
		`((DEFPROP ,FN
			   ,(DPB (- (LENGTH (THIRD ARGS))
				    (LENGTH (MEMQ '&REST (THIRD ARGS))))
				 0606 77)
			   ARGS-INFO)))
	       (T `((DEFPROP ,FN
			     ,(DPB (LENGTH (THIRD ARGS)) 0606 (LENGTH (THIRD ARGS)))
			     ARGS-INFO))))
       #-cadr
       (LET ((SYMBOL-INDEX (- (GET ',FN 'QLVAL) 200))
	     (SI:%INHIBIT-READ-ONLY T))
	 (SETF (SI:MICRO-CODE-SYMBOL-NAME-AREA SYMBOL-INDEX) ',FN)))))


(defflavor prolog-flavor () ())

(defflavor read-only-variable (cell) (prolog-flavor)
  :initable-instance-variables
  :gettable-instance-variables
  :settable-instance-variables)

(defflavor source-variable (name cell) (prolog-flavor)
  :gettable-instance-variables
  :initable-instance-variables)

(defflavor source-ro-variable (name cell) (prolog-flavor)
  :gettable-instance-variables
  :initable-instance-variables)

(defflavor lisp-locative (cell) (prolog-flavor)
  :gettable-instance-variables
  :initable-instance-variables)

(defflavor clause (templates
		   (committing nil)
		   predicator
		   (name "No name")
		   contains-cut
		   (prover 'clause-prover-not-compiled)	;obsolete default.
		   world)
	     (prolog-flavor)
    :settable-instance-variables
    :initable-instance-variables
    :gettable-instance-variables)

(defflavor lambda-clause (templates) (prolog-flavor)
    :initable-instance-variables
    :gettable-instance-variables)
