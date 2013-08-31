;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;; This is LM-Prolog's compiler. It uses "copying pure code" and success 
;;; continuations. Optimizations include exclusive case detection, attempts to 
;;; avoid untrailing, input unifications before output ones, detection of 
;;; determinacy, and tail recursion.

;;; Micro-compilation of predicates is also available on a VERY experimental basis.
;;; You say (:COMPILE-METHOD :MICRO-COMPILED . u), where  u  is (), (T), or
;;; (:DYNAMIC), corresponding to desired :DEPEND-ON-BEING-MICROCOMPILED dependency.
;;; You say (MA-LOAD-PREDICATORS . predicators) to install the frobs.

(eval-when (compile eval load)
(defun constant-p (object)
    (or (numberp object) (stringp object) (null object) (eq object t)
	(and (consp object) (eq 'quote (car object)))))
)

(defvar local-variable-names (make-array 128.)
  "List of standardized variable names.")

(dotimes (i 128.)
  (setf (aref local-variable-names i)
        (intern (format nil "?VARIABLE~d" i) 'prolog))
  (putprop (aref local-variable-names i) i ':compiled-local-variable))

(defprop .continuation. t :compiled-local-variable)

(defconst *definition-compile-unify-predication*
          (create-definition
            'ignore 'ignore 'ignore 'ignore
            '(:options (:compile-method :intrinsic compile-unify-predication))
	    'ignore 'ignore))

(defconst *definition-initvars-predication*
          (create-definition
            'ignore 'ignore 'ignore 'ignore
            '(:options (:compile-method :intrinsic compile-initvars-predication))
            'ignore 'ignore))

(defconst *definition-compile-cut*
          (create-definition
            'ignore 'ignore 'ignore 'ignore
            '(:options (:compile-method :intrinsic compile-cut))
            'ignore 'ignore))


; Compile time representation of terms:
; They are like at runtime.
; Variables use the name field to keep the following information:
; The car holds the access form used in the Lisp code to access the variable.
; The cdr is a plist. A weakness of the scheme is that we can't keep track of
; first/subsequent occurrence in the plist.

;(defsubst value-cell-name (value-cell)
;  (rest1 (%make-pointer dtp-list value-cell)))

(defvar *compiler-symbol-table* :unbound "A symbol table for the compiler.  Values are plists.")

(defsubst value-cell-name (value-cell)
  (gethash value-cell *compiler-symbol-table*))

(defsubst set-value-cell-name (value-cell info)
  (puthash value-cell info *compiler-symbol-table*))

(defsubst value-cell-index (v)
  (get (value-cell-name v) ':index))

(defsubst value-cell-access-form (v)
  (car (value-cell-name v)))

(defsubst value-cell-declaration (v)
  (get (value-cell-name v) ':declaration))

(defun value-cell-declaration-hack (v)
  (let ((d (value-cell-declaration v)))
    (cond ((eq d '-) (setf (value-cell-declaration v) '*)))
    d))

(defsubst value-cell-path (v)
  (get (value-cell-name v) ':path))

(defun value-cell-local-ref (v)
  (no-dereference (value-cell-access-form v)))

(defvar *need-so-far* ':unbound "# logical variables needed in the compiled code.")

;(defun compiler-cell (&rest plist)
;  (let* ((index (1- (incf *need-so-far*)))
;	 (cell
;	   (%cell `((%dereference ,(aref local-variable-names index))
;		    :index ,index ,@(copylist plist)))))
;    (or (value-cell-declaration cell)
;	(setf (value-cell-declaration cell) '*))
;    cell))

(defun compiler-cell (&rest plist)
  (let* ((index (1- (incf *need-so-far*)))
	 (cell (%cell0)))
    (set-value-cell-name cell
			 `((%dereference ,(aref local-variable-names index))
			   :index ,index ,@(copylist plist)))
    (or (value-cell-declaration cell)
	(setf (value-cell-declaration cell) '*))
    cell))

(defsubst compile-time-void-p (x)
  (and (value-cell-p x) (equal '(%cell0) (value-cell-access-form x))))

(defsubst born-variable-p (x)
  (and (value-cell-p x) (atom (value-cell-name x))))

; Database hackery.

(defun compilers-definition (predicator &optional world)
  (cond ((eq *predicator-being-defined* predicator)
         (create-definition
	   'ignore 'ignore 'ignore 'ignore *options* 'ignore 'ignore))
        ((eq 'unify-predication predicator) *definition-compile-unify-predication*)
        ((eq 'initvars-predication predicator) *definition-initvars-predication*)
        ((eq 'cut predicator) *definition-compile-cut*)
        (world (definition-in-world predicator world))
	((COMPILER:FILE-DECLARATION PREDICATOR 'PROLOG-DEFINITION))
        (t (current-definition predicator nil))))

(defmacro current-entrypoint (predicator-form) ;;the fast, cached way, for symbols
  (cond ((eq predicator-form '*predicator-being-defined*) `*c-prover*)
	((constant-p predicator-form)
	 `(%current-entrypoint
	    ,predicator-form (sharp-comma (locf (definitions ,predicator-form)))))
        (t `(definition-prover (current-definition ,predicator-form)))))

(deffun entrypoint-in-world (predicator &optional world)
  (let ((predicator (lisp-form-1 predicator ':dont-invoke)))
    (cond ((symbolp predicator)
	   (cond ((null world) (current-entrypoint predicator))
		 ((let ((definition (definition-in-world predicator world)))
		    (definition-prover
		      (or definition
			  (undefined-predicate predicator (list world))))))))
	  ((typep predicator 'lambda-clause)
	   (let-closed ((*instance* predicator)) #'resolve-lambda-clause))
	  ((entrypoint-in-world
	     (prolog-error ':predicator-not-symbolic
			   "the predicator ~S should be a symbol"
			   predicator)
	     world)))))

(defun condition-for-compile-clause (options)
  (or (eq ':dynamic (option-value ':type options))
      (option-value ':indexing-patterns options)))

(defmacro using-compiler-resource (&body body)
  `(using-resource (*compiler-symbol-table* symbol-table)
     (using-resource (a-trail trail 500.)
       (with-trail a-trail
	 (with-new-*vector* 
	   ,@body)))))

(defun make-compiler-definition (predicator-being-defined options clauses indexes-name)
  (using-compiler-resource
    (make-compiler-definition-1 predicator-being-defined options clauses indexes-name)))

(defun make-compiler-definition-1 (*predicator-being-defined* *options* clauses indexes-name)
        
  (cond ((and (eq ':keep (option-value ':if-old-definition *options*))
	      (not (option-value ':type *options* ())))
	 (setq *options* `(:options (:type :dynamic) ,@(cdr *options*)))))

  (let* (contributions computed-determinacy *top-predication*
	 (*need-so-far* 0)
	 (world (option-value ':world *options*))
         (type (option-value ':type *options*))
	 (argument-list (option-value ':argument-list *options*))
         (prover-name (prolog-db-symbol *predicator-being-defined* world 'prover))
         (prover-form `',prover-name)
	 (declared-determinacy
	   (declared-determinacy *predicator-being-defined* *options* ':defining)))

    (let-if (neq world (first *universe*)) ((*universe* (cons world *universe*)))
      
      ;;Substantially more optimizations to do for :static predicates.
      (cond ((and (eq type ':static) (null clauses))
	     (cond ((and (eq ':ignore (option-value ':if-another-definition *options*))
			 (not (option-value ':deterministic *options* ())))
		    (setq *options* `(:options (:deterministic :always) ,@(cdr *options*)))))
	     (setq *top-predication* (top-predication-etc argument-list 0. 1000.)
		   computed-determinacy t))
	    ((eq type ':static)
	     (multiple-value-bind (min-call-pattern-length max-call-pattern-length)
		 (arity-range clauses 1000. 0.)
	       (multiple-value-bind (top-predication
				     top-discriminator
				     most-general-predication
				     most-general-discriminator)
		   (cond ((neq argument-list (option-value ':argument-list ()))
			  (top-predication-etc argument-list 0. 1000.))
			 (t
			  (top-predication-etc argument-list
					       min-call-pattern-length
					       max-call-pattern-length)))
		 (setq *top-predication* top-predication)
		 (multiple-value-bind (mgd-instances t-instances)
		     (head-instances-etc most-general-predication
					 most-general-discriminator
					 top-discriminator
					 *trail* clauses () ())
		   (mark-committing-clauses mgd-instances clauses most-general-discriminator)
		   (mapc
		     #'(lambda (t-d-var)
			 (let ((n (find-position-in-list t-d-var top-discriminator)))
			   (cond ((some t-instances
					#'(lambda (t-i)
					    (cond ((listp t-i)
						   (not
						     (value-cell-p (nth n t-i))))))))
				 ((eq (value-cell-declaration t-d-var) '+)
				  (setf (value-cell-declaration t-d-var) '*)))))
		     top-discriminator)))
	       
	       ;;Compute a decent arglist for on-line documentation.
	       (cond ((neq argument-list (option-value ':argument-list ())))
		     ((= min-call-pattern-length max-call-pattern-length)
		      (setq *options*
			    `(:options (:argument-list ,(make-list min-call-pattern-length ':initial-value '*))
				       ,@(cdr *options*))))
		     ((let ((contribution
			      (make-list (1+ min-call-pattern-length)
					 ':initial-value '*)))
			(setf (nth min-call-pattern-length contribution) '&rest)
			(setq *options* `(:options (:argument-list ,contribution) ,@(cdr *options*))))))
	       
	       ;;Determinacy analysis under the assumption that all calls to
	       ;; predicate-being-defined are deterministic.  Justify this with a
	       ;;  least-fixpoint argument...
	       ;;Issue run time warnings for predicates going nondeterministic.
	       (setq computed-determinacy
		     (and ;;Intrinsics decide determinacy themselves.
		       ;;They have clauses because they need a prover.
		       ;;Typically just one clause with head  predication.
		       (not (memq ':intrinsic (option-value ':compile-method *options*)))
		       (let ((*options* `(:options (:deterministic :always) ,@(cdr *options*))))
			 (every clauses
				#'(lambda (clause)
				    (let* ((template (send clause ':templates))
					   (ignore	;7.11
					     (%construct (car template))))
				      (det-conjuncts-p
					(%construct (cdr template))
					(send clause ':committing))))))))
	       (cond ((and computed-determinacy
			   (not declared-determinacy)
			   (eq ':ignore (option-value ':if-another-definition *options*))
			   (not (option-value ':deterministic *options* ())))
		      (setq *options* `(:options (:deterministic :always) ,@(cdr *options*))))
		     ((and (not computed-determinacy) (not declared-determinacy))
		      (push `(warn-if-was-deterministic ',*predicator-being-defined* ',world)
			    contributions))))))
      
      (cond ((not (condition-for-compile-clause *options*))
	     (setq contributions
		   (add-contribution
		     (compile-relation
		       prover-name
		       *top-predication*
		       clauses
		       (and declared-determinacy (not computed-determinacy)))
		     contributions)))
	    (t
	     (let ((scratch-name
		     (prolog-db-symbol
		       *predicator-being-defined* world "SCRATCH")))
	       (cond ((eq ':flush (option-value ':if-old-definition *options*))
		      (setq prover-form
			    (make-interpreter-definition
			      *predicator-being-defined*
			      *options*
			      indexes-name))))
	       (setq contributions
		     (add-alternating-defun-and-revision
		       scratch-name 0 (length clauses) clauses contributions)))))
      
      (values prover-form `',*options* contributions))))

(deffun mark-committing-clauses (mgd-instances clauses most-general-discriminator)
  (cond ((null (cdr clauses))
	 (send (car clauses) ':set-committing t))
	(t (cond ((eq (car mgd-instances) '/?)
		  (prolog-warn ':wrong-argument-list-declaration
			       ':implausible
			       "The argument list declared for ~S is ~
		       incompatible with some clause. The clause will fail."
			       *predicator-being-defined*)
		  (send (car clauses) ':set-committing t))
		 ((some (cdr mgd-instances)
			#'(lambda (mgd-i2)
			    (compatible
			      (car mgd-instances) mgd-i2 most-general-discriminator))))
		 (t (send (car clauses) ':set-committing t)))
	   (mark-committing-clauses
	     (cdr mgd-instances) (cdr clauses) most-general-discriminator))))

;NOT REALLY UNIFICATION...
(DEFFUN COMPATIBLE (X Y DISCRIMINATOR)
  (COND ((NULL X))
	((COMPATIBLE-1 (CAR X) (CAR Y) (CAR DISCRIMINATOR))
	 (COMPATIBLE (CDR X) (CDR Y) (CDR DISCRIMINATOR)))))

(DEFFUN COMPATIBLE-1 (X Y DIS)
  (OR (VALUE-CELL-P X)
      (VALUE-CELL-P Y)
      (AND (CONSP X) (CONSP Y)
	   (OR (NEQ '&REST (VALUE-CELL-DECLARATION DIS))
	       (COMPATIBLE-1 (CDR X) (CDR Y) DIS)))
      (EQUAL X Y)))

(deffun arity-range (clauses min max)
  (cond ((null clauses) (values min max))
	((let* ((head-template (car (send (car clauses) ':templates)))
		(l (template-length head-template)))
	   (arity-range (cdr clauses)
			(min min l)
			(max max (cond ((template-dotted-p head-template) (1+ l))
				       (l))))))))

#+PROLOG-MICRO-CODE
(DEFFUN TEMPLATE-LENGTH (TEMPLATE)
  (COND ((CONSP TEMPLATE) (1+ (TEMPLATE-LENGTH (CDR TEMPLATE))))
	((FAST-LOCATIVE-P TEMPLATE)
	 (1- (LENGTH (CONS 0 (CONTENTS TEMPLATE)))))
	(T 0)))

#-PROLOG-MICRO-CODE
(deffun template-length (template)
  (selectq (first template)
    (0 (1- (length template)))
    (3 (1+ (template-length (rest2 template))))
    (otherwise 0)))

#+PROLOG-MICRO-CODE
(DEFFUN TEMPLATE-DOTTED-P (TEMPLATE)
  (COND ((CONSP TEMPLATE) (TEMPLATE-DOTTED-P (CDR TEMPLATE)))
	((FAST-LOCATIVE-P TEMPLATE)
	 (CDR (LAST (CONS 0 (CONTENTS TEMPLATE)))))
	(T TEMPLATE)))

#-PROLOG-MICRO-CODE
(deffun template-dotted-p (template)
  (selectq (car template)
    (0 (cdr (last template)))
    (3 (template-dotted-p (cddr template)))
    (otherwise t)))

(deffun top-predication-etc (arglist min max
				     &optional top-predication top-discriminator
				     mg-predication mg-discriminator)
  (cond ((null arglist)
	 (values (prolog-cons *predicator-being-defined*
			      (nreverse top-predication))
		 top-discriminator
		 (nreverse mg-predication)
		 mg-discriminator))
	((atom arglist)
	 (prolog-ferror ':arglist-syntax-error
			"~%Dotted pair in argument-list option: ~S"
			(option-value ':argument-list *options*))
	 (top-predication-etc () min max
	   top-predication
	   top-discriminator
	   mg-predication
	   mg-discriminator))
	((consp (first arglist))
	 (multiple-value-bind (mgp mgd)
	     (top-predication-sub (car arglist) () ())
	   (let ((cell (compiler-cell ':declaration '+)))
	     (top-predication-etc (cdr arglist) min max
	       (prolog-cons cell top-predication)
	       (prolog-cons cell top-discriminator)
	       (prolog-cons mgp mg-predication)
	       (nconc mgd mg-discriminator)))))
	(t
	 (selectq (aref (string (first arglist)) 0)
             (#/& (cond ((< (length top-predication) min)
			 (top-predication-etc (prolog-cons '* arglist) min max
			   top-predication top-discriminator
			   mg-predication mg-discriminator))
			((< min max)
			 (let ((cell (compiler-cell ':declaration '&REST)))
			   ;don't have to dereference &rest arg
			   (setf (value-cell-access-form cell)
				 (value-cell-local-ref cell))
			   (values
			     (prolog-cons *predicator-being-defined*
					  (prolog-rev-append
					   top-predication cell))
			     (prolog-cons cell top-discriminator)
			     (prolog-rev-append mg-predication cell)
			     (prolog-cons cell mg-discriminator))))
			((top-predication-etc () min max
			   top-predication top-discriminator
			   mg-predication mg-discriminator))))
	     (#/+ (let ((cell (compiler-cell ':declaration '+)))
		   (top-predication-etc (cdr arglist) min max
		     (prolog-cons cell top-predication)
		     (prolog-cons cell top-discriminator)
		     (prolog-cons cell mg-predication)
		     (prolog-cons cell mg-discriminator))))
             (#/- (let ((cell (compiler-cell ':declaration '-)))
		   (top-predication-etc (cdr arglist) min max
		     (prolog-cons cell top-predication) top-discriminator
		     (prolog-cons cell mg-predication) mg-discriminator)))
             (t (let ((cell (compiler-cell ':declaration '*)))
		   (top-predication-etc (cdr arglist) min max
		     (prolog-cons cell top-predication) top-discriminator
		     (prolog-cons cell mg-predication) mg-discriminator)))))))

(deffun top-predication-sub (arglist mg-predication mg-discriminator)
  (cond ((null arglist)
	 (values (nreverse mg-predication) mg-discriminator))
	((atom arglist)
	 (prolog-ferror ':arglist-syntax-error
			"~%Dotted pair in argument-list option: ~S"
			(option-value ':argument-list *options*))
	 (top-predication-sub () mg-predication mg-discriminator))
	((consp (first arglist))
	 (multiple-value-bind (mgp mgd)
	     (top-predication-sub (car arglist) () ())
	   (top-predication-sub (cdr arglist)
				(prolog-cons mgp mg-predication)
				(nconc mgd mg-discriminator))))
	((selectq (aref (string (first arglist)) 0)
	   (#/& (let ((cell (%cell0)))
		  (values
		    (prolog-rev-append mg-predication cell)
		    (prolog-cons cell mg-discriminator))))
	   (#/+ (let ((cell (%cell0)))
		  (top-predication-sub (cdr arglist) 
		   (prolog-cons cell mg-predication)
		   (prolog-cons cell mg-discriminator))))
	   (t (top-predication-sub (cdr arglist)
	       (prolog-cons (%cell0) mg-predication)
	       mg-discriminator))))))

(deffun prolog-rev-append (head tail)
  (cond ((null head) tail)
	(t (prolog-rev-append
	    (cdr head)
	    (prolog-cons (car head) tail)))))

(deffun head-instances-etc (mgp mgd td mark clauses mgd-is t-is)
  (cond ((null clauses)
	 (values (nreverse mgd-is) (nreverse t-is)))
	((%unify-term-with-template mgp (car (send (car clauses) ':templates)))
	 (let* (*variables-alist* (mgd-i (copy-term-1 mgd)) (t-i (copy-term-1 td)))
	   (untrail mark)
	   (head-instances-etc
	     mgp mgd td mark (cdr clauses) (cons mgd-i mgd-is) (cons t-i t-is))))
	(t ;warning here
	   (untrail mark)
	   (head-instances-etc
	     mgp mgd td mark (cdr clauses) (cons '/? mgd-is) (cons '/? t-is)))))

(deffun add-alternating-defun-and-revision
	(scratch-name clause/# out-of clauses contributions)
  (cond (clauses
	 (let ((name-or-/#
		 (cond ((symbolp (send (first clauses) ':name))
			(send (first clauses) ':name))
		       (t clause/#))))
	   (add-alternating-defun-and-revision
	     scratch-name (1+ clause/#) out-of (rest1 clauses)
	     `(,@contributions
	       (defun ,scratch-name ,@(cdr (compile-clause-1 (car clauses))))
	       (revise-clause
		 ',scratch-name ',name-or-/# ,out-of ',*options* ',*predicator-being-defined*)))))
	(t contributions)))

(defvar *c-prover* nil "The name of the defun being generated.")

(defvar *need-in-disjunction* ':unbound
  "New value of *need-so-far* being computed.")

(defvar *cut-tag-alist* ()
  "Alist of pairs ( occurrence . tag ). It records the lexical environment of occurrences of (CUT).")

(defvar *cut-use-alist* ()
  "Alist of pairs ( tag . thrown-p ). ``Allocated'' by TOP-DISJUNCTION and used by COMPILE-CUT.")

(defun compile-clause (clause)
  (using-compiler-resource
    (compile-clause-1 clause)))


(defun compile-clause-1 (clause)
  (let* ((*need-so-far* 0)
	 (*cut-tag-alist* *cut-tag-alist*)
	 (*cut-use-alist* (cons (cons '*cut-tag* nil) *cut-use-alist*))
	 (cell (compiler-cell ':declaration '&REST)))
    ;don't have to dereference &rest arg
    (setf (value-cell-access-form cell)	   ;7.12'
	  (value-cell-local-ref cell))
    (multiple-value-bind (if then)
        (conjunction (resolve (prolog-cons *predicator-being-defined* cell) clause)
                     `(invoke .continuation.)
                     ())
      (let ((formal-argument-list (formal-argument-list nil (list cell))))
        `(lambda
           (,@formal-argument-list
            &aux
            ,@(nset-difference (union () (continuation-variables (cons if then)))
                               formal-argument-list))
           ,(throwify if then (send clause ':contains-cut)))))))

(defun throwify (if then cut)
  (cond (cut `(cond (,if (*throw ,(caar *cut-use-alist*) ,@then))))
	(then `(cond (,if ,@then)))
	(t if)))

(DEFFUN FORMAL-ARGUMENT-LIST (DET TOP-ARGS)
  (COND ((NULL DET) (CONS '.CONTINUATION. (FORMAL-ARGUMENT-LIST T TOP-ARGS)))
	((NULL TOP-ARGS) ())
	((VALUE-CELL-P TOP-ARGS) (LIST '&REST (VALUE-CELL-LOCAL-REF TOP-ARGS)))
	(T (CONS (VALUE-CELL-LOCAL-REF (CAR TOP-ARGS))
		 (FORMAL-ARGUMENT-LIST DET (CDR TOP-ARGS))))))

(DEFUN MA-LOAD-PREDICATORS (&REST PREDICATORS)
  (APPLY 'COMPILER:MA-LOAD
	 (MAPCAN
	   #'(LAMBDA (P) (COPYLIST (GET (CURRENT-ENTRYPOINT P) 'ALL-EXCISED)))
	   PREDICATORS)))

(DEFVAR *EXCISE-LIST*)

(defun add-contribution (item contributions)
  (cond ((and (consp item)
	      (equal (car item) 'progn)
	      (equal (cadr item) ''compile))
	 `(,@contributions ,@(cddr item)))
	(t `(,@contributions ,item))))

(defun compile-relation (*c-prover* top-predication clauses determinacy)
  (cond (clauses (compile-relation-1 top-predication clauses determinacy))
	(t (let ((compile-method (option-value ':compile-method *options*))
		 (defun-form `(defun ,*c-prover* (&rest ignore))))
	     (cond ((eq ':micro-compiled (car compile-method))
		    `(local-declare ((compiler:microcompile ,*c-prover* t))
		       (eval-when (compile load eval)
			 (defprop ,*c-prover* ,(cadr compile-method)
				  :depend-on-being-microcompiled))
		       ,defun-form))
		   (t defun-form))))))

(defun compile-relation-1 (top-predication clauses determinacy)
  (let* ((formal-argument-list (formal-argument-list NIL (cdr top-predication)))
	 (initial-bindings (+-variables-dereferences (cdr top-predication)))
	 (INNER-CALL (INNER-CALL DETERMINACY (CDR TOP-PREDICATION)))
	 (INNER-FORMALS (INNER-FORMALS DETERMINACY (CDR TOP-PREDICATION)))
	 (CODE
           `(let ,initial-bindings
	      ,(cond (determinacy `(cond (,INNER-CALL (invoke .continuation.))))
		     (t INNER-CALL))))
	 (SUBST-BODY
	   (TOP-DISJUNCTION TOP-PREDICATION CLAUSES
			    (COND (DETERMINACY '(CONTINUATION (TRUE))) (T '.CONTINUATION.))))
	 (SUBST-FORMS
	   `((EVAL-WHEN (COMPILE EVAL)
	       (DEFFSUBST ,(CAR INNER-CALL) ,INNER-FORMALS
		 (COMMENT :PREDICATOR ,*PREDICATOR-BEING-DEFINED*
			  :ARGUMENT-LIST
			  ,(INNER-ARGUMENT-LIST DETERMINACY (CDR TOP-PREDICATION)))
		 ,SUBST-BODY)))))
    (cond ((memq '&rest formal-argument-list)
	   ;;Is it a predicate a la COMMENT that ignores all arguments?
	   (let ((rest-argument (caar (last (cadr CODE)))))
	     (cond ((not (contains SUBST-BODY rest-argument))
		    (setf (cadr CODE) (butlast (cadr CODE)))
		    (setf (cadr (memq '&rest formal-argument-list)) 'ignore))))))
    (LET ((DEFUN-FORM
	    `(DEFUN ,*c-prover* (,@formal-argument-list
				 &AUX ,@(nset-difference
					  (union () (continuation-variables SUBST-BODY))
					  INNER-FORMALS))
	      ,code))
	  (COMPILE-METHOD (OPTION-VALUE ':COMPILE-METHOD *OPTIONS*)))
      (COND ((EQ ':MICRO-COMPILED (CAR COMPILE-METHOD))
	     (LET (*EXCISE-LIST*)
	       (MAPC #'EXCISE-INTERNAL-FUNCTIONS (CDDR DEFUN-FORM))
	       (LET ((ALL-EXCISED (CONS *C-PROVER* (MAPCAR #'CADR *EXCISE-LIST*))))
	       `(LOCAL-DECLARE
		  ,(MAPCAR #'(LAMBDA (F) `(COMPILER:MICROCOMPILE ,F T))
			   ALL-EXCISED)
		  (EVAL-WHEN (COMPILE LOAD EVAL)
		    (DEFPROP ,*C-PROVER* ,(CADR COMPILE-METHOD)
			     :DEPEND-ON-BEING-MICROCOMPILED))
		  (DEFPROP ,*C-PROVER* ,ALL-EXCISED ALL-EXCISED)
		  ,@SUBST-FORMS
		  ,DEFUN-FORM
		  ,@*EXCISE-LIST*))))
	    (T `(PROGN 'COMPILE ,@SUBST-FORMS ,DEFUN-FORM))))))

(DEFUN INNER-ARGUMENT-LIST (DET TOP-ARGS)
  (CONS DET (INNER-ARG-LIST TOP-ARGS)))

(DEFUN INNER-ARG-LIST (TOP-ARGS)
  (COND ((NULL TOP-ARGS) ())
	((VALUE-CELL-P TOP-ARGS) '(&REST))
	((+P (VALUE-CELL-DECLARATION (CAR TOP-ARGS)))
	 (CONS '+ (INNER-ARG-LIST (CDR TOP-ARGS))))
	((CONS '* (INNER-ARG-LIST (CDR TOP-ARGS))))))

(DEFUN INNER-CALL (DET TOP-ARGS)
  (LET ((INNER-NAME
	  (PROLOG-DB-SYMBOL *PREDICATOR-BEING-DEFINED*
			    (OPTION-VALUE ':WORLD *OPTIONS*)
			    'INNER)))
    (COND (DET (CONS INNER-NAME (INNER-CALL-1 TOP-ARGS)))
	  (T (LIST* INNER-NAME '.CONTINUATION. (INNER-CALL-1 TOP-ARGS))))))

(DEFFUN INNER-CALL-1 (TOP-ARGS)
  (COND ((NULL TOP-ARGS) ())
	((VALUE-CELL-P TOP-ARGS) (INNER-CALL-1 (LIST TOP-ARGS)))
	((CONS (VALUE-CELL-LOCAL-REF (CAR TOP-ARGS))
	       (INNER-CALL-1 (CDR TOP-ARGS))))))

(DEFFUN INNER-FORMALS  (DET TOP-ARGS)
  (COND ((NULL DET) (CONS '.CONTINUATION. (INNER-FORMALS T TOP-ARGS)))
	((NULL TOP-ARGS) ())
	((VALUE-CELL-P TOP-ARGS) (LIST (VALUE-CELL-LOCAL-REF TOP-ARGS)))
	(T (CONS (VALUE-CELL-LOCAL-REF (CAR TOP-ARGS)) (INNER-FORMALS DET (CDR TOP-ARGS))))))

(DEFFUN EXCISE-INTERNAL-FUNCTIONS (CODE)
  (COND ((CONSP CODE)
         (SELECTQ (CAR CODE)
	   (QUOTE)
	   (FUNCTION
	    (AND (CONSP (CADR CODE))
		 (EQ 'LAMBDA (CAADR CODE))
		 (LET ((G (PROLOG-INTERN "~A-~A" *C-PROVER* (GENSYM))))
		   (MAPC #'EXCISE-INTERNAL-FUNCTIONS (CDDADR CODE))
		   (PUSH `(DEFUN ,G ,@(CDADR CODE)) *EXCISE-LIST*)
		   (SETF (CADR CODE) G))))
	   (CONTINUATION
	    (LET ((MEXP (MACROEXPAND CODE)))
	      (COND ((CONSP MEXP)
		     (PLAIN-DISPLACE CODE MEXP)
		     (EXCISE-INTERNAL-FUNCTIONS CODE)))))
           (OTHERWISE (MAPC #'EXCISE-INTERNAL-FUNCTIONS CODE))))))

(deffun +-variables-dereferences (arglist &optional bindings)
  (cond ((null arglist) (nreverse bindings))
	((value-cell-p arglist)
	 (cond (*unsafe-rest-argument*
		(setf (value-cell-access-form arglist)
		      `(rest-arg-copy ,(value-cell-access-form arglist))))
	       (t (setf (value-cell-access-form arglist)
			`(rest-arg-fixup ,(value-cell-access-form arglist)))))
	 (+-variables-dereferences (list arglist) bindings))
	((+P (value-cell-declaration (car arglist)))
	 (let ((access-form (value-cell-access-form (car arglist)))
	       (gensym (compiler-gensym)))
	   (setf (value-cell-access-form (car arglist)) gensym)
	   (+-variables-dereferences
	     (cdr arglist) `((,gensym ,access-form) ,@bindings))))
	((+-variables-dereferences (cdr arglist) bindings))))

(defmacro make-if (form)
  `(multiple-value-bind (if then) ,form `(cond (,if ,@then))))

(defun trivial-continuation-p (cont)
  (let ((cont (macroexpand cont)))
    (cond ((atom cont))
	  ((eq 'quote (car cont)))
	  #+lexical
	  ((eq 'function (car cont)) (atom (cadr cont))))))

;CUT is very tricky since it is lexically scoped. The following hack works for now.
;We use two specials:
;       *CUT-TAG-ALIST* of pairs ( occurrence . tag )
;                       bound here and pushed by RESOLVE. It records the lexical environment
;                       of an occurrence of (CUT).
;       *CUT-USE-ALIST* of pairs ( tag . thrown-p )
;                       is bound-pushed here, the latest tag is used as above, and
;                       COMPILE-CUT uses both alists to see if it has to throw, if so
;                       sets thrown-p to t.
(defun top-disjunction (predication clauses continuation)
  (let* ((tag (cond ((trivial-continuation-p continuation) continuation)
                    (t (compiler-gensym))))
         (*need-in-disjunction* *need-so-far*)
         (*cut-tag-alist* *cut-tag-alist*)
         (*cut-use-alist* (cons (cons tag nil) *cut-use-alist*))
         (inner
           (cond ((null clauses) ())
                 ((null (rest1 clauses))
                  (make-if
		    (top-conjunction predication (car clauses) continuation)))
                 (t `(cond ,@(disjunction predication clauses tag)))))
         (outer (cond ((cdar *cut-use-alist*) `(*catch ,tag ,inner))
                      (t inner)))
         (let-bindings `(,@(cond ((and (neq tag continuation)
                                       (or (rest1 clauses)
                                           (cdar *cut-use-alist*)))
                                  `((,tag ,continuation))))
                         ,@(cond ((and (consp inner)
                                       (member '((progn (untrail mark) nil))
					       inner))
                                  '((mark *trail*)))))))
    (setq *need-so-far* *need-in-disjunction*)
    (cond (let-bindings `(let ,let-bindings ,outer)) (t outer))))

(defun disjunction (predication clauses continuation)
  (multiple-value-bind (if then deep-p)
      (top-conjunction predication (car clauses) continuation)
    `((,if ,@then)
      ,@(and deep-p (cdr clauses) `(((progn (untrail mark) nil))))
      ,@(and (cdr clauses) (disjunction predication (cdr clauses) continuation)))))

(deffun deep-backtrack-p (predications deep)
  (cond ((eq predications 'impossible) nil)
	((null predications) deep)
        ((atom predications) t)
        ((atom (car predications)) t)
        (t (selectq (caar predications)
             (unify-predication
	      (cond ((let ((*need-so-far* (second (first predications))))
		       (deep-backtrack-unify-predication-p
			 (fourth (first predications)))))
		    ((not (third (first predications)))
		     (or (fifth (first predications))
			 (deep-backtrack-p (rest1 predications) deep)))))
             (initvars-predication (deep-backtrack-p (cdr predications) deep))
             (cut nil)
             (t t)))))

(defun not-subsequent-occurrence-p (term)
  (cond ((compile-time-void-p term))
	((not (< (value-cell-index term) *need-so-far*)))))

;;; Format of UNIFY-PREDICATION is a list 
;;; (UNIFY-PREDICATION ,need-so-far ,det-p ,+-unification-plist ,non-+-unification-plist ,variables-declared-unbound)

(defun deep-backtrack-unify-predication-p (pairs)	;Compiler bug, cant use DEFFUN here.
  (cond (pairs
	 (let* ((term (second pairs)))
	   (cond ((and (atom term) (not (value-cell-p term)))
		  (deep-backtrack-unify-predication-p (rest2 pairs)))
		 ((and (value-cell-p term) (not-subsequent-occurrence-p term))
		  (SI:%BIND (LOCF (VALUE-CELL-INDEX TERM)) -1)
		  (deep-backtrack-unify-predication-p (rest2 pairs)))
		 ((and (consp term)
		       (value-cell-p (car term))
		       (not-subsequent-occurrence-p (car term))
		       (progn (SI:%BIND (LOCF (VALUE-CELL-INDEX (CAR TERM))) -1) t)
		       (value-cell-p (cdr term))
		       (not-subsequent-occurrence-p (cdr term))
		       (progn (SI:%BIND (LOCF (VALUE-CELL-INDEX (CDR TERM))) -1) t))
		  (deep-backtrack-unify-predication-p (rest2 pairs)))
		 (t t))))))

(defun top-conjunction (predication clause continuation)
  (let* ((*need-so-far* *need-so-far*)
         (resolvent (resolve predication clause))
	 (DEEP (DEEP-BACKTRACK-P
		 RESOLVENT (NOT (MEMQ (CAREFUL-FIRST (MACROEXPAND CONTINUATION))
				      '(QUOTE FUNCTION))))))
     (multiple-value-bind (if then)
         (conjunction resolvent `(invoke ,continuation) ())
       (setq *need-in-disjunction* (max *need-so-far* *need-in-disjunction*))
       (values if then deep))))

(defvar *predication* ':unbound
  "The predication being compiled - sometimes needed by :intrinsics.")

(defun conjunction (predications if then &optional world-form)
  (cond ((eq predications 'impossible) (values nil then))
        ((null predications) (values if then))
        ((atom predications)
	 (VALUES `(PROVE-CONJUNCTION-IF-NEED-BE
		    ,(CONSTRUCTOR PREDICATIONS T)
		    (CONTINUATION ,IF))
		 THEN))
        ((atom (car predications))
         (multiple-value-bind (if1 then1) (conjunction (cdr predications) if then)
           (values `(lexpr-funcall
                      ,(cond (world-form
                              `(entrypoint-in-world
                                 (car ,(constructor (car predications) t))
                                 ,world-form))
                             (t
                              `(entrypoint-in-world
                                 (car ,(constructor (car predications) t)))))
                      (continuation ,if1)
                      (cdr ,(constructor (car predications) t)))
                   then1)))
        (t (multiple-value-bind (if1 then1)
               (conjunction (cdr predications) if then)
             (compile-predication (car predications) if1 then1
                                  (and (symbolp (caar predications))
                                       (definition-options
                                         (compilers-definition
                                           (caar predications))))
                                  world-form)))))

(defun compile-predication (*predication* if then options &optional world-form)
  (let ((compile-method (option-value ':compile-method options)))
    (selectq (first compile-method)
      (:INTRINSIC
       (cond ((eq 'and (car *predication*))
              (conjunction (cdr *predication*) if then))
             ((value-cell-p (cdr (last *predication*)))
              (compile-predication *predication* if then
                                   `(:options (:compile-method :CLOSED))))
             (t (lexpr-funcall (second compile-method) if then (cdr *predication*)))))
      (:OPEN
       (let ((definition (compilers-definition (car *predication*))))
         (values (cond ((and (declared-determinacy (car *predication*) options)
                             (not (cheap-p if)))
                        `(and ,(top-disjunction *predication*
						(definition-clauses definition)
						`(continuation (true)))
                              ,if))
                       (t (top-disjunction *predication*
					   (definition-clauses definition)
					   `(continuation ,if))))
                 then)))
      (t (multiple-value-bind (caller arglist)
             (mapcar1* #'constructor (cdr *predication*))
           (let ((entry-point-form
                   (cond (world-form
                          `(entrypoint-in-world
			     ,(constructor (car *predication*) t) ,world-form))
                         ((value-cell-p (car *predication*))
			  `(entrypoint-in-world ,(constructor (car *predication*) t)))
			 ((AND (EQ ':MICRO-COMPILED (CAR COMPILE-METHOD))
			       (CADR COMPILE-METHOD))
			  `',(prolog-db-symbol (car *predication*)
					       (option-value ':world options)
					       'prover))
                         (t `(current-entrypoint ,(constructor (car *predication*) t))))))
             (values (cond ((and (symbolp (car *predication*))
                                 (declared-determinacy (car *predication*) options)
                                 (not (cheap-p if)))
                            `(and (,caller
				   ,entry-point-form (continuation (true)) ,@arglist) ,if))
                           (t `(,caller
				,entry-point-form (continuation ,if) ,@arglist)))
                     then)))))))

(defun compile-unify-predication
       (if then *need-so-far* det-p +-plist non-+-plist unbound-variables)
  (mapc #'(lambda (v) (setf (value-cell-declaration v) '-)) unbound-variables)
  (let* ((u-+-code (unify-pairs +-plist))
	 (u-non-+-code (unify-pairs non-+-plist)))
    (mapc #'(lambda (v) (setf (value-cell-declaration v) '-)) unbound-variables)
    (cond (det-p (values `(and ,@u-+-code) `((and ,@u-non-+-code ,if ,@then))))
	  (t (values `(and ,@u-+-code ,@u-non-+-code ,if) then)))))

(defun unify-pairs (pairs-of-form-and-template)
  (cond (pairs-of-form-and-template
         `(,(compile-unify-for-one-argument
	      (value-cell-access-form (first pairs-of-form-and-template))
	      (second pairs-of-form-and-template)
	      (value-cell-declaration-hack (first pairs-of-form-and-template)))
           ,@(unify-pairs (rest2 pairs-of-form-and-template))))))

(defun compile-unification (form term)
  (cond ((consp form)
	 (let ((g (gensym)))
	   `(let ((,g ,form))
	      ,(compile-unify-for-one-argument g term '+))))
	(t (compile-unify-for-one-argument form term '+))))

(DEFUN DECLARATION-CAR (D) (COND ((CONSP D) (CAR D)) (T '*)))

(DEFUN DECLARATION-CDR (D) (COND ((CONSP D) (CDR D)) ((EQ D '&REST) D) (T '*)))

(defun compile-unify-for-one-argument (remote local declaration)
  (cond (#-prolog-micro-code t
	 #+prolog-micro-code
	 (EQ ':MICRO-COMPILED (CAR (OPTION-VALUE ':COMPILE-METHOD *OPTIONS*)))
	 (compile-unify-for-one-argument-without-ucode remote local declaration))
	(t (compile-unify-for-one-argument-with-ucode remote local declaration))))

;#-prolog-micro-code
(progn 'compile
(deffun mapterm-2 (f term)
  (cond ((value-cell-p term)
	 (or (compile-time-void-p term)
	     (< (value-cell-index term) *need-so-far*)
	     (funcall f term)))
	((consp term)
	 (mapterm-2 f (car term)) (mapterm-2 f (cdr term)))))

(defvar *value-cell-names* nil "Only used below.")

(defun compile-unify-construct (remote local declaration)
  (let (*value-cell-names*
	(constructor (constructor local t)))
    (mapterm-2 #'(lambda (x) (push `(setq ,(value-cell-local-ref x) (%cell0))
				   *value-cell-names*))
	       local)
    (COND ((EQUAL REMOTE CONSTRUCTOR) `T)
	  (T `(progn ,@*value-cell-names*
		     ,(cond
			;((and (eq '- declaration) (constant-p constructor))
			; `(bind-cell ,remote ,constructor))
			;LOSES FOR FLAVOR INSTANCES AND GENERATES A LOT OF CODE
			((eq '- declaration)
			 `(bind-cell-check ,remote ,constructor))
			((and (value-cell-p local)
			      (eq '- (value-cell-declaration-hack local)))
			 `(bind-cell-check ,constructor ,remote))
			((constant-p constructor)
			 `(unify-without-occur-check ,remote ,constructor))
			(t `(unify ,remote ,constructor))))))))

(defvar *recursion-threshold* 2 "stop depth for inline unification code gen.")

(defun compile-unify-for-one-argument-without-ucode
       (remote local declaration &optional (recursion-depth 0))
  ;;This implements a heuristic for when to bind REMOTE to a local variable
  ;; to avoid e.g. repeated use of %dereference
  (cond ((or (atom remote) (atom local) (eq declaration '-))
	 (compile-unify-for-one-argument-inner
	   remote local declaration recursion-depth))
	(t `(let ((remote ,remote))
	      ,(compile-unify-for-one-argument-inner
		 'remote local declaration recursion-depth)))))

(defun compile-unify-for-one-argument-inner
       (remote local declaration RECURSION-DEPTH)
  ;; compile code to unify REMOTE - an already compiled form
  ;;                  with LOCAL  - a term from the source code
  (cond
    ((value-cell-p local)
     (let* ((unifier
              (cond ((compile-time-void-p local) t)
                    ((< (value-cell-index local) *need-so-far*)
		     (compile-unify-construct remote local declaration))
                    (T (SETF (VALUE-CELL-INDEX LOCAL) -1)
		       (OR (EQUAL REMOTE (VALUE-CELL-LOCAL-REF LOCAL))
			   `(progn (setq ,(value-cell-local-ref local) ,remote)
				   t))))))
       unifier))
    ((consp local)
     (let* ((unifier
	      (COND ((> RECURSION-DEPTH *RECURSION-THRESHOLD*)
		     (COMPILE-UNIFY-CONSTRUCT REMOTE LOCAL declaration))
		    (T
		     (LET ((BASE-CASES
			     (cond ((-P DECLARATION)
				    `((,(or (eq declaration '-) `(%uvar-p ,remote))
				       ,@(CDR (COMPILE-UNIFY-CONSTRUCT
						REMOTE LOCAL '-)))))))
			   (REC-CASES
			     (cond ((neq declaration '-)
				    `((,(or (consp declaration) `(consp ,remote))
				       (and ,(compile-unify-for-one-argument-without-ucode
					       `(car ,remote)
					       (car local)
					       (DECLARATION-CAR DECLARATION)
					       (+ 3 RECURSION-DEPTH))
					    ,(compile-unify-for-one-argument-without-ucode
					       `(cdr ,remote)
					       (cdr local)
					       (DECLARATION-CDR DECLARATION)
					       (1+ RECURSION-DEPTH)))))))))
		       `(COND ,@REC-CASES ,@BASE-CASES))))))
       ;;Needs to be done here too, since this functions doesn't always traverse
       ;;LOCAL fully.
       (MAPTERM-2 #'(LAMBDA (X) (SETF (VALUE-CELL-INDEX X) -1)) LOCAL)
       unifier))
    ((+P declaration)
     (cond ((symbolp local) `(eq ,remote ',local))
	   (t `(equal ,remote ',local))))
    ;((eq '- declaration) `(bind-cell ,remote ',local))
    ;LOSES FOR FLAVOR INSTANCES AND GENERATES A LOT OF CODE
    (t `(uvar-constant ,remote ',local))))

(defmacro uvar-constant (x y)
  (cond ((atom x) `(%uvar-constant ,x ,y))
	(t `(let ((remote ,x)) (%uvar-constant remote ,y)))))
)

#+prolog-micro-code
(PROGN 'COMPILE

(defsubst %uvar-constant (x y) (unify x y))
(defsubst bind-cell-check (x y) (unify x y))
(defsubst unify-without-occur-check (x y) (unify x y))

(defun compile-unify-for-one-argument-with-ucode (remote local declaration)
  ;; compile code to unify REMOTE - an already compiled form
  ;;                  with LOCAL  - a term from the source code
  (cond ((and (+P declaration) (consp local) (not-ground-p local))
	 `(and ,(or (consp declaration) `(consp ,remote))
	       ,(compile-unify-for-one-argument-with-ucode
		  `(car ,remote)
		  (car local)
		  (declaration-car declaration))
	       ,(compile-unify-for-one-argument-with-ucode
		  `(cdr ,remote)
		  (cdr local)
		  (declaration-cdr declaration))))
	(t (let ((constructor (macroexpand (template-constructor local))))
	     (cond ((and (+P declaration) (constant-p constructor))
		    (cond ((symbolp local) `(eq ,remote ,constructor))
			  ((atom local) `(equal ,remote ,constructor))
			  (t `(unify-without-occur-check ,remote ,constructor))))
		   (t (compile-unify-default remote constructor local)))))))

(defun compile-unify-default (remote constructor local)
  (cond ((constant-p constructor) `(unify ,remote ,constructor))
	((selectq (careful-first constructor)
	   (quote `(UNIFY-WITHOUT-OCCUR-CHECK ,remote ,constructor))
	   (occurrence
	    (selectq (cadr constructor)
	      (1 (OR (EQUAL REMOTE (VALUE-CELL-LOCAL-REF LOCAL))
		     `(progn (setq ,(value-cell-local-ref local) ,remote) t)))
	      (2 (OR (EQUAL REMOTE (VALUE-CELL-ACCESS-FORM LOCAL))
		     `(unify ,(value-cell-access-form local) ,remote)))))
	   (VOID t)
	   (otherwise
	    `(%unify-term-with-template
	       ,(no-dereference remote) ,(ENSURE-template constructor)))))))

(DEFUN ENSURE-TEMPLATE (CONSTRUCTOR)
  (LET ((LOCALS (ENSURE-TEMPLATE-LOCALS CONSTRUCTOR ())))
    (COND (LOCALS `(LET ,(MAPCAR #'(LAMBDA (P) (LIST (CDR P) (CAR P))) LOCALS)
		     (MAKE-TEMPLATE ,CONSTRUCTOR)))
	  (T `(MAKE-TEMPLATE ,CONSTRUCTOR)))))

(DEFFUN ENSURE-TEMPLATE-LOCALS (CONSTRUCTOR LOCALS)
  (COND ((ATOM CONSTRUCTOR) LOCALS)
	((SELECTQ (CAR CONSTRUCTOR)
	   ((QUOTE FUNCTION) LOCALS)
	   (OCCURRENCE
	    (COND ((ATOM (THIRD CONSTRUCTOR)) LOCALS)
		  ((ASSOC (THIRD CONSTRUCTOR) LOCALS)
		   (SETF (THIRD CONSTRUCTOR)
			 (CDR (ASSOC (THIRD CONSTRUCTOR) LOCALS)))
		   LOCALS)
		  (T (ENSURE-TEMPLATE-LOCALS
		       CONSTRUCTOR
		       `((,(THIRD CONSTRUCTOR) . ,(GENSYM)) ,@LOCALS)))))
	   (T (ENSURE-TEMPLATE-LOCALS (CDR CONSTRUCTOR)
				      (ENSURE-TEMPLATE-LOCALS (CAR CONSTRUCTOR)
							      LOCALS)))))))

(defun template-constructor (target)
  (multiple-value-bind (flag thing)
      (si:backquotify (template-constructor-1 target))
    (si:backquotify-1 flag thing)))

(defun template-constructor-1 (x)
  (cond ((compile-time-void-p x) `(,SI:**BACKQUOTE-/,-FLAG** . (VOID)))
	((value-cell-p x)
	 (let ((local-ref (value-cell-local-ref x)))
	   `(,SI:**BACKQUOTE-/,-FLAG** .
	     ,(cond ((< (value-cell-index x) *need-so-far*)
		     `(occurrence 2 ,local-ref))
		    (t (SETF (VALUE-CELL-INDEX X) -1)
		       `(occurrence 1 ,local-ref))))))
        ((atom x) x)
        (t (cons (template-constructor-1 (car x))
                 (template-constructor-1 (cdr x))))))
)

;;New fancy code to delay %cell-allocations as long as possible.

(defun compile-initvars-predication (if then &rest vector)
  (let ((code `(,if ,@then)))
    (clear-path vector)
    (traverse-path code vector ())
    (let ((plist (install-cell-allocations vector)))
      (values (cond (plist `(PROGN (setq ,@plist) ,if)) (t if)) then))))

(deffun clear-path (vector)
  (cond (vector
	 (cond ((value-cell-p (car vector))
		(setf (value-cell-path (car vector)) 'nopath)))
	 (clear-path (cdr vector)))))

(deFFun traverse-path (code vector PATH)
  (cond ((consp code)
         (selectq (first code)
	   ((quote function))
           (continuation
	    (traverse-path (second code) vector (CONS CODE PATH)))
           (otherwise (mapc #'traverse-path
			    code (circular-list vector) (circular-list PATH)))))
	((get code ':compiled-local-variable)
	 (let ((cell
		 (car (mem #'(lambda (code x) (eq code (value-cell-local-ref x)))
			   code vector))))
	   (cond (cell (setf (value-cell-path cell)
			     (most-general-path (value-cell-path cell)
						PATH))))))))

(deffun install-cell-allocations (vector)
  (cond (vector
         (cond ((and (value-cell-p (first vector))
                     (not (compile-time-void-p (first vector))))
                (let ((path (value-cell-path (first vector))))
                  (cond ((consp path)
                         (let ((inner (second (first path)))) ;;a body of a cont.
                           (selectq (first (first path))
                             (continuation
                              (plain-displace
                                (first path)
                                `(LET
                                   ((,(value-cell-local-ref (first vector))
				     (%cell0)))
                                   (continuation ,inner))))
                             ((LET LET*)
                              (push
                                `(,(value-cell-local-ref (first vector))
				  (%cell0))
                                (rest1 inner)))))
                         (install-cell-allocations (rest1 vector)))
                        (t `(,(value-cell-local-ref (first vector))
			     (%cell0)
                             ,@(install-cell-allocations (rest1 vector)))))))
               (t (install-cell-allocations (rest1 vector)))))))

(deffun most-general-path (path1 path2)
  (and path1 path2
       (cond ((eq 'nopath path1) path2)
             ((eq 'nopath path2) path1)
             ((memq (first path1) path2))
             (t (most-general-path (rest1 path1) path2)))))

;; Old simple-minded code was:
;(defun compile-initvars-predication (if then &rest cells)
;  (values `(progn (setq ,@(initvars-pairs cells)) ,if) then))
;
;(defun initvars-pairs (vector)
;  (cond (vector
;        (cond ((and (value-cell-p (first vector))
;                    (consp (value-cell-name (first vector))))
;               `(,(first (value-cell-name (first vector)))
;                 (%cell ',(second (value-cell-name (first vector))))
;                 ,@(initvars-pairs (rest1 vector))))
;              (t (initvars-pairs (rest1 vector)))))))
;

(deffun det-conjuncts-p (conjuncts sofar)
  (cond ((null conjuncts) sofar)
        ((atom conjuncts) nil)
        ((consp (car conjuncts))
         (selectq (caar conjuncts)
	   (unwind-protect
	    (det-conjuncts-p (cdr conjuncts)
			     (det-conjuncts-p (list (cadar conjuncts)) sofar)))
           (cut (det-conjuncts-p (cdr conjuncts) t))
           (and (det-conjuncts-p (cdr conjuncts)
                                 (det-conjuncts-p (cdar conjuncts) sofar)))
           (cases (det-conjuncts-p
                    (cdr conjuncts)
                    (every (cdar conjuncts)
                           #'(lambda (case) (det-conjuncts-p case sofar)))))
           (either (det-conjuncts-p
                     (cdr conjuncts)
                     (every (cdar conjuncts)
                            #'(lambda (case)
                                (det-conjuncts-p (list case) sofar)))))
           (rules (det-conjuncts-p
                    (cdr conjuncts)
                    (every (cddar conjuncts)
                           #'(lambda (rule)
                               (det-conjuncts-p (cdr rule) sofar)))))      
           (or (det-conjuncts-p
                 (cdr conjuncts)
                 (every (cdar conjuncts)
                        #'(lambda (case)
                            (det-conjuncts-p
			      (list case)		;7.11
                              (and sofar
                                   (eq case (car (last (car conjuncts))))))))))
           (t (det-conjuncts-p (cdr conjuncts)
                               (and (symbolp (caar conjuncts))
                                    (declared-determinacy
                                      (caar conjuncts)
                                      (definition-options
                                        (compilers-definition
                                          (caar conjuncts))))
                                    sofar)))))
        (t (det-conjuncts-p (cdr conjuncts) nil))))

(defun compile-call (if then predication &optional world)
  (cond ((null world)
         (conjunction `(,predication) if then))
        (t (conjunction `(,predication) if then (constructor world t)))))

(defun cheap-p (form)
  (cond ((null (cdr form)))
        ((eq 'invoke (car form))
         (cond ((symbolp (cadr form)))
               ((eq 'continuation (caadr form)) (cheap-p (cadadr form)))))))

(defun compile-cut (if then &optional arg)
  (cond ((eq arg '*locally*)
         (values `(true) `((cond (,if ,@then)))))
        (t
         (let ((tag (cdr (assq *predication* *cut-tag-alist*))))
           (cond ((eq tag (caar *cut-use-alist*))
                  (values `(true) `((cond (,if ,@then)))))
                 (t (setf (cdr (assq tag *cut-use-alist*)) t)
                    (values `(true) `((*throw ,tag (cond (,if ,@then)))))))))))

(defun compile-lisp-form (x &optional mode)
  (cond ((value-cell-p mode)
	 (compile-lisp-form-1 x #'lisp-form-constructor (constructor mode t)))
	(t (selectq mode
	     (:copy
	      (list-if-need-be
		(compile-lisp-form-1 x #'lisp-form-constructor '':copy)
		'let '((*prolog-work-area* working-storage-area))))
	     (:invoke
	      (compile-lisp-form-1 x #'lisp-form-constructor '':invoke))
	     (:query
	      (compile-lisp-form-1 x #'lisp-form-constructor '':query))
	     (:dont-invoke
	      (compile-lisp-form-1 x #'lisp-form-constructor '':dont-invoke))
	     (nil
	      (compile-lisp-form-1 x #'constructor))
	     (t (prolog-ferror ':bad-lisp-form-mode
			       "~s should be :copy :invoke :query or :dont-invoke"
			       mode))))))

(defun list-if-need-be (last &rest elements)
  ;;If LAST is a quoted thing, dont make a list.
  (cond ((or (atom last) (eq 'quote (car last))) last)
	(t (append elements (list last)))))

(defun lisp-form-constructor (target &optional ignore)
  (declare (special *lisp-form-mode-form*))
  (mapterm #'(lambda (x)
	       `(lisp-form-1 ,(value-cell-access-form x) ,*lisp-form-mode-form*))
	   target))

;;This is needed for e.g. (< ...) predications to compile sensibly.
(DEFUN LEXPR-FUNCALL-ON-LIST-IN-AREA (FORM)
  ;;compiler:lexpr-funcall-on-list missed this...
  (LET ((LASTARG (macroexpand (CAR (LAST FORM)) NIL)))
   (let-if (eq (careful-first lastarg) 'rest-arg-fixup)
	   ((lastarg (cons (caadr lastarg) (cdadr lastarg))))
    (COND ((ATOM LASTARG) FORM)
	  ((memq (CAR LASTARG) '(%prolog-list LIST-IN-AREA))
	   `(FUNCALL ,@(BUTLAST (CDR FORM)) . ,(no-reference-list (cddr lastarg))))
	  ((memq (CAR LASTARG) '(%prolog-list* LIST*-IN-AREA))
	   `(LEXPR-FUNCALL ,@(BUTLAST (CDR FORM)) . ,(no-reference-list (cddr lastarg))))
	  ((EQ (CAR LASTARG) 'cons-IN-AREA)
	   `(LEXPR-FUNCALL ,@(BUTLAST (CDR FORM))
			   . ,(no-reference-list (butlast (cdr lastarg)))))
	  ((EQ (CAR LASTARG) 'prolog-cons)
	   `(LEXPR-FUNCALL ,@(BUTLAST (CDR FORM))
			   . ,(no-reference-list (cdr lastarg))))
	  ((EQ (CAR LASTARG) 'quote)
	   `(FUNCALL ,@(BUTLAST (CDR FORM)) . ,(second lastarg)))
	  (T FORM)))))

(defun no-reference-list (x)
  (mapcar 'force-dereference x))

(deffun force-dereference (x)
  (cond ((and (symbolp x) (get x ':compiled-local-variable))
	 `(%dereference ,x))
	((atom x) x)
	(t (selectq (car x)
	     ((%dereference %reference)
	      (force-dereference (cadr x)))
	     (t `(%dereference ,x))))))

(compiler:add-optimizer lexpr-funcall lexpr-funcall-on-list-in-area)

(compiler:add-optimizer apply lexpr-funcall-on-list-in-area)

(defun compile-lisp-form-1 (x constructor &optional *lisp-form-mode-form*)
  (declare (special *lisp-form-mode-form*))
  (compile-lisp-form-2 x constructor))

(deffun compile-lisp-form-2 (x constructor)
  (cond ((value-cell-p x) `(eval ,(funcall constructor x t)))
        ((consp x)
         (cond ((eq 'quote (first x)) (funcall constructor (second x) t))
               ((value-cell-p (cdr (last x)))
		(compile-lisp-form-3
		  `(lexpr-funcall ',(first x) ,@(rest1 x)) constructor))
	       ((value-cell-p (first x))
		(compile-lisp-form-3
		  `(funcall ',(first x) ,@(rest1 x)) constructor))
               (t (compile-lisp-form-3 x constructor))))
        (t x)))

(defun compile-lisp-form-3 (x constructor)
  (cond ((null x) ())
	((value-cell-p x) `((mapcar #'eval ,(funcall constructor x t))))
	(t (cons (compile-lisp-form-2 (car x) constructor)
		 (compile-lisp-form-3 (cdr x) constructor)))))

(defun compile-lisp-predicate (if then pred &optional lisp-form-mode)
  (values `(and ,(compile-lisp-form pred lisp-form-mode) ,if) then))

(defun compile-lisp-command (if then pred &optional lisp-form-mode)
  (values `(progn ,(compile-lisp-form pred lisp-form-mode) ,if) then))

(defun compile-lisp-value (if then value form &optional mode)
  (values `(and ,(compile-unification (compile-lisp-form form mode) value) ,if)
	  then))

(defun compile-or-internal (if then &rest disjuncts)
  (values (top-disjunction 'ignore (mapcar #'ncons disjuncts) `(continuation ,if))
          then))

(defun compile-and-internal (if then &rest conjuncts)
  (conjunction conjuncts if then))

(defun compile-repeat (if then &optional (times #o37777777))
  (values `(let ((mark *trail*))
             (dotimes (i ,(compile-lisp-form `',times ':dont-invoke))
               (and ,if (return t))
               (untrail mark)))
          then))

;Make this conditional w.r.t. *UNSAFE-REST-ARGUMENT* which is true if no risk for 
;dangling pointers.
(defun unwind-protect-emitter (if then mess-predication &rest cleanup-predications)
  (multiple-value-bind (code1 code2)
      (conjunction `(,mess-predication) if then)
    (values
      (COND (*UNSAFE-REST-ARGUMENT*
	     `(let ((cleanup
		      (continuation
			,(make-if (conjunction cleanup-predications `(false) ())))))
		(trail cleanup)
		,code1))
	    ((let* (*variables-alist*
		    (cleanup-relocated (relocate cleanup-predications)))
	       `(let* ,(relocate-body)
		  (let ((cleanup
			  (continuation
			    ,(make-if (conjunction cleanup-relocated `(false) ())))))
		    (trail cleanup)
		    ,code1)))))
     code2)))


(defun cases-emitter (if then &rest cases)
  (let* ((flag (compiler-gensym))
         (used-flag-p nil)
         (inner
           (mapcar
             #'(lambda (x)
                 (cond ((eq x (car (last cases)))
                        (cond (used-flag-p
                               `((lisp-predicate (not (car ,flag)) :dont-invoke)
                                 ,@x))
                              (t x)))
                       ((det-conjuncts-p (list (car x)) t)
                        `(,@(cond (used-flag-p
                                   `((lisp-predicate (not (car ,flag))
                                                     :dont-invoke))))
                          ,(car x) (cut *locally*) ,@(cdr x)))
                       (t (setq used-flag-p t)
                          `((lisp-predicate (not (car ,flag)) :dont-invoke)
                            ,(car x)
                            (lisp-command (setf (car ,flag) t) :dont-invoke)
                            ,@(cdr x)))))
             cases))
         (det-p (and (det-conjuncts-p (list *predication*) t)
		     (not (cheap-p if))))
         (disjunction-continuation
           (cond (det-p `(continuation (true)))
                 (t `(continuation ,if))))
         (inner2
           (cond (used-flag-p
                  `(with-stack-list (,flag nil)
                     ,(top-disjunction 'ignore inner disjunction-continuation)))
                 (t (top-disjunction 'ignore inner disjunction-continuation)))))
    (values
      (cond (det-p `(and ,inner2 ,if)) (t inner2))
      then)))

(defun rules-emitter (if then term &rest rules)
  (let* ((det-p (and (det-conjuncts-p (list *predication*) t)
		     (not (cheap-p if))))
         (disjunction-continuation
           (cond (det-p `(continuation (true)))
                 (t `(continuation ,if))))
         (inner2
           (top-disjunction
             'ignore
             (mapcar #'(lambda (x)
                         `((= ,term ,(car x)) (cut *locally*) ,@(cdr x)))
                     rules)
             disjunction-continuation)))
  (values
    (cond (det-p `(and ,inner2 ,if)) (t inner2)) 
    then)))

(defun either-emitter (if then &rest cases)
  (lexpr-funcall #'cases-emitter if then (mapcar #'ncons cases)))

(defun compiler-gensym ()
  (let ((g (gensym))) (putprop g t ':compiled-local-variable) g))

(defun compile-with (if then condition &rest predications)
  (cond ((atom condition)
         (compile-predication *predication* if then
			      '(:options (:compile-method :closed))))
        (t (let ()
             (selectq (car condition)
               (universe
		(compile-with-lisp-value	;7.11
		  (COMPILE-LISP-FORM `',(cadr condition) ':COPY)
		  predications if then '*universe*))
               (protected-worlds
                (compile-with-lisp-value	;7.11
                  (constructor (cadr condition) t)
                  predications if then
                  '*protected-worlds*))
               (interrupts
                (compile-with-lisp-value	;7.11
                  `(eq ':off ,(constructor (cadr condition) t))
                  predications if then
                  'inhibit-scheduling-flag))
               (circularity-mode
                (compile-double-unwind-protect
                  (constructor (cadr condition) t)
                  predications if then '*circularity-mode* 'set-circularity-mode))
               (undefined-predicate-mode
                (compile-double-unwind-protect
                  (constructor (cadr condition) t)
                  predications if then '*undefined-predicate-mode* 'set-undefined-predicate-mode))
               (lisp-value
                (compile-with-lisp-value	;7.11
                  (compile-lisp-form `',(cadr condition) (cadddr condition))
                  predications if then
		  (compile-lisp-form (caddr condition))))
               ;;AND and OPTION to come
               (otherwise
                (compile-predication *predication* if then
                                     '(:options (:compile-method :closed)))))))))

(defun compile-make-true (if then condition)
  (cond ((atom condition)
         (compile-predication *predication* if then
			      '(:options (:compile-method :closed))))
        (t (let ()
             (selectq (car condition)
               (universe
		(values `(progn (setf *universe* ,(compile-lisp-form `',(cadr condition) ':copy)) ,if)
			then))
               (protected-worlds
		(values `(progn (setf *protected-worlds* ,(constructor (cadr condition) t)) ,if)
			then))
               (interrupts
		(values `(progn (setf inhibit-scheduling-flag (eq ':off ,(constructor (cadr condition) t))) ,if)
			then))
               (circularity-mode
		(values `(progn (set-circularity-mode ,(constructor (cadr condition) t)) ,if)
			then))
               (undefined-predicate-mode
                (values `(progn (set-undefined-predicate-mode ,(constructor (cadr condition) t)) ,if)
			then))
               (lisp-value
		(values `(progn (setf ,(compile-lisp-form (caddr condition))
				      ,(compile-lisp-form `',(cadr condition) (cadddr condition)))
				,if)
			then))
               ;;AND and OPTION to come
               (otherwise
                (compile-predication *predication* if then
                                     '(:options (:compile-method :closed)))))))))

(defun compile-let (if then condition)
  (cond ((atom condition)
         (compile-predication *predication* if then
			      '(:options (:compile-method :closed))))
        (t (let ()
             (selectq (car condition)
               (universe
		(compile-let-lisp-value
		  (COMPILE-LISP-FORM `',(cadr condition) ':COPY)
		  if then '*universe*))
               (protected-worlds
                (compile-let-lisp-value
                  (constructor (cadr condition) t)
                  if then
                  '*protected-worlds*))
               (interrupts
                (compile-let-lisp-value
                  `(eq ':off ,(constructor (cadr condition) t))
                  if then
                  'inhibit-scheduling-flag))
               (circularity-mode
                (compile-single-unwind-protect
                  (constructor (cadr condition) t)
                  if then '*circularity-mode* 'set-circularity-mode))
               (undefined-predicate-mode
                (compile-single-unwind-protect
                  (constructor (cadr condition) t)
                  if then '*undefined-predicate-mode* 'set-undefined-predicate-mode))
               (lisp-value
                (compile-let-lisp-value
                  (compile-lisp-form `',(cadr condition) (cadddr condition))
                  if then
		  (compile-lisp-form (caddr condition))))
               ;;AND and OPTION to come
               (otherwise
                (compile-predication *predication* if then
                                     '(:options (:compile-method :closed)))))))))

(defun compile-with-lisp-value			;7.11
        (value-form predications if then access-form)
  (let* ((g1 (compiler-gensym))
         (g2 (compiler-gensym))
         (undo `(progn (trail (continuation (setf ,access-form ,g2)))
                       (invoke ,g1)
		       ,if))
         (code
           `(let ((,g1 (lisp-value-resetter (locf ,access-form))) (,g2 ,value-form))
              (trail ,g1)
	      (setf ,access-form ,g2)
              ,(make-if (conjunction predications undo ())))))
    (values code then)))

(defun compile-double-unwind-protect
        (value-form predications if then access-form &rest clobberers)
  (let* ((g1 (compiler-gensym))
         (g2 (compiler-gensym))
         (undo `(progn (trail (continuation (,@clobberers ,g2)))
                       (,@clobberers ,g1)
		       ,if))
         (code
           `(let ((,g1 ,access-form) (,g2 ,value-form))
              (trail (continuation (,@clobberers ,g1)))
              (,@clobberers ,g2)
              ,(MAKE-IF (conjunction predications undo ())))))
    (values code then)))

(defun compile-let-lisp-value (value-form if then access-form)
  (let* ((g1 (compiler-gensym))
         (code
           `(let ((,g1 (lisp-value-resetter (locf ,access-form))))
              (trail ,g1)
	      (setf ,access-form ,value-form)
	      ,if)))
    (values code then)))

(defun compile-single-unwind-protect (value-form if then access-form &rest clobberers)
  (let* ((g1 (compiler-gensym))
         (code
           `(let ((,g1 ,access-form))
              (trail (continuation (,@clobberers ,g1)))
              (,@clobberers ,value-form)
              ,if)))
    (values code then)))

(defun lisp-value-resetter (location)
  (let ((loc (list-in-area *prolog-work-area* ':location location))
	(value (cond ((location-boundp location) (cdr location))
		     (t ':unbound))))
    (continuation (funcall 'lisp-value-reset loc value))))

(defun lisp-value-reset (location value)
  (cond ((neq value ':unbound)
	 (rplacd (cadr location) value))
	(t (location-makunbound (cadr location)))))

(defun mapcar1* (function list) ;;Like MAPCAR on one list but works on nonstrict
 ;;lists too. Returns (i) FUNCALL/LEXPR-FUNCALL (ii) mapped list.
  (cond ((null list) (values 'funcall ()))
        ((atom list) (values 'lexpr-funcall (list (funcall function list t))))
        (t (multiple-value-bind (caller values) (mapcar1* function (cdr list))
             (values caller (cons (funcall function (car list)) values))))))

;;Strategy for compiling unification:
;;RESOLVE is called with a goal and a clause to be resolved with at runtime.
;;Its task is to break down the unification problem into several <variable,pattern> pairs,
;;and to return an instance of the body of the clause.
(defun resolve (predication clause)
  (cond ((eq predication 'ignore) clause)
        (t (let* ((mark *trail*)
		  (clause-template (send clause ':templates))
		  (unbounds (unbounds-in predication ())))
	     (with-stack-list (*vector* . #.(make-list 64.))
	       (unwind-protect
		 (cond ((%unify-term-with-template (rest1 predication)
						   (first clause-template))
			(+-allocate mark mark)	;7.12
			(let* ((need *need-so-far*)
			       (+unifications (unify-arguments #'+p mark))
			       (-unifications (unify-arguments #'-p mark))
			       (ignore (collect-cells *vector* ()))
			       (body-predications
				 (%construct (rest1 clause-template)))
			       (init2 (collect-cells *vector* ()))
			       (ignore (untrail mark)))
			  (with-stack-list*
			    (all +unifications -unifications body-predications)
			    (let* ((init1 (collect-voids all () ())))
			      (collect-cuts body-predications)
			      `(,@(and init1 `((initvars-predication ,@init1)))
				(unify-predication
				  ,need
				  ,(and (send clause ':committing)    ;not when open compiling
					(eq *predicator-being-defined*	;8
					    (send clause ':predicator)))
				  ,+unifications	;7.12
				  ,-unifications
				  ,unbounds)
				,@(and init2 `((initvars-predication ,@init2)))
				,@body-predications)))))
		       (t 'impossible))
		 (untrail mark)))))))

;;Be smart about patterns like (?x . ?y) when matched against a `+' variable V.
;;Simply equate ?x to (car V) and ?y to (cdr V).
;;It is correct to do this if no previous use of ?x and ?y,
;;because such previous uses would assume that V is a cons which it might not be.
;;Also, be smart about matching a second occurrence of ?x against a variable V.
;;Simply equate ?x and V.
(deffun +-allocate (mark begmark)
  (cond ((< mark *trail*)
	 (let ((item (aref *trail-array* mark)))
	   (COND ((AND (NOT (BORN-VARIABLE-P ITEM)) (BORN-VARIABLE-P (CDR ITEM)))
		  (SET-VALUE-CELL-NAME (CDR ITEM) (VALUE-CELL-NAME ITEM)))
		 ((and (+p (value-cell-declaration item)) (consp (cdr item)))
		  (cond ((and (born-variable-p (cadr item))
			      (+-occur-check (cadr item) mark begmark))
			 (set-value-cell-name
			   (cadr item)
			   `((car ,(value-cell-local-ref item))
			     :index ,*need-so-far* :declaration *))))
		  (cond ((and (born-variable-p (cddr item))
			      (+-occur-check (cddr item) mark begmark))
			 (set-value-cell-name
			   (cddr item)
			   `((cdr ,(value-cell-local-ref item))
			     :index ,*need-so-far* :declaration *)))))))
	 (+-allocate (1+ mark) begmark))))

(deffun +-occur-check (x mark begmark)
  (or (= begmark mark)
      (and (or (-p (value-cell-declaration (aref *trail-array* begmark)))
	       (occur-check x (cdr (aref *trail-array* begmark))))
	   (+-occur-check x mark (1+ begmark)))))

(deffun collect-cells (vector sofar)
  (cond ((null vector) sofar)
	((born-variable-p (car vector))
	 (set-value-cell-name (car vector) (value-cell-name (compiler-cell)))
	 (collect-cells (cdr vector) (cons (car vector) sofar)))
	(t (collect-cells (cdr vector) sofar))))

;Singe-occurrence variables may turn out to occur more than once.
;Properly allocate newly born single-occurrence variables.
(deffun collect-voids (term tails sofar)
  (cond ((born-variable-p term)
	 (set-value-cell-name term (copylist '((%cell0) :declaration -)))
	 sofar)
	((compile-time-void-p term)
	 (cond ((occurs-in term tails)
		(set-value-cell-name term (value-cell-name (compiler-cell)))
		(cons term sofar))
	       (t sofar)))
	((consp term)
	 (collect-voids (cdr term) tails
	   (with-stack-list* (tails (cdr term) tails)
	     (collect-voids (car term) tails sofar))))
	(t sofar)))

(deffun unify-arguments (p mark)
  (cond ((< mark *trail*)
	 (let* ((local (aref *trail-array* mark)))
	   (cond ((funcall p (value-cell-declaration local))
		  `(,local
		    ,(contents local)
		    ,@(unify-arguments p (1+ mark))))
		 (t (unify-arguments p (1+ mark))))))))

(deffun unbounds-in (x sofar)
  (cond ((consp x)
         (unbounds-in (cdr x) (unbounds-in (car x) sofar)))
        ((and (value-cell-p x) (eq '- (value-cell-declaration-hack x)))
	 (cons x sofar))
        (t sofar)))

(deffun collect-cuts (term)
  (cond ((consp term)
         (cond ((equal term '(cut))
                (or (assq term *cut-tag-alist*)
                    (push (cons term (caar *cut-use-alist*)) *cut-tag-alist*)))
               (t (collect-cuts (first term)) (collect-cuts (rest1 term)))))))

#+(and prolog-micro-code) #8r compiler:
(progn 'compile

(defun (:property prolog:make-template p2) (argl dest)
  (let ((item
	  (cond ((prolog:qc-file-in-progress)
		 `(,compiler:eval-at-load-time-marker make-template-body ',(first argl)))
		(t (make-template-body (first argl))))))
    (outi `(move ,dest (quote-vector ',item)))))


(defun make-template-body (form)
  (let ((area #-CommonLisp si:fasl-constants-area #+CommonLisp si:macro-compiled-program)
	(si:%inhibit-read-only t))
    (selectq (first form)
      (prolog:void `20000000)
      (prolog:occurrence
       (let ((occ/# (second (second form)))
	     (form (third form)))
	 (selectq (car form)
	   (lexical-ref (%logdpb (1- occ/#) 2503 (%logdpb 3 2302 (cadr form))))
	   (local-ref
	    (let ((ref (fifth (cadr form))))
	      (selectq (first ref)
		(arg (%logdpb (1- occ/#) 2503 (%logdpb 1 2302 (second ref))))
		((local locblock) (%logdpb (1- occ/#) 2503 (%logdpb 2 2302 (second ref))))
		(t (break "BAD-LOCAL-REF")))))
	   (T (BREAK "BAD-REF-CLASS")))))
      (quote (%make-pointer dtp-locative (copytree (cdr form) area)))
      (list
       (copylist (mapcar #'make-template-body (cdr form)) area))
      ((cons list*)
       (lexpr-funcall 'list*-in-area area (mapcar #'make-template-body (cdr form))))
      (t (break "BAD-TEMPLATE-FORM")))))
)

;; FLUSHED AS OF 9.2.
;;Determinacy.
;;People can have (DECLARE (DETERMINISTIC foo bar) (NON-DETERMINISTIC baz ...) ...) now.
;;
;;(defun :deterministic fexpr (symbols)
;;       (mapc #'deterministic-1 symbols))
;;
;;(defun deterministic-1 (symbol)
;;  ;;simple-minded for now
;;  (push (list ':deterministic symbol) compiler:file-local-declarations))
;;
;;(defun :non-deterministic fexpr (symbols)
;;       (mapc #'non-deterministic-1 symbols))
;;
;;(defun non-deterministic-1 (symbol)
;;  (push (list ':non-deterministic symbol) compiler:file-local-declarations))
;;  
(defun declared-determinacy (ignore-predicator options &optional (using-or-defining ':using))
    (cond
;;  ;;assuming for now that there are no declarations that mask each other
;;        ((mem #'(lambda (predicator item)
;;                  (and (eq ':deterministic (car item))
;;                       (eq predicator (cadr item))))
;;              predicator
;;              compiler:file-local-declarations))
;;        ((mem #'(lambda (predicator item)
;;                  (and (eq ':non-deterministic (car item))
;;                       (eq predicator (cadr item))))
;;              predicator
;;              compiler:file-local-declarations)
;;         nil)
	(t
	 (let-if (eq ':using using-or-defining) ((*default-options* ()))
	   (eq ':always (prolog:option-value ':deterministic options))))))

(defun warn-if-was-deterministic (predicator world)
  (let ((definition (definition-in-world predicator world)))
    (and definition
         (definition-deterministic definition)
         (format t "~&Predicate ~a in ~a used to be deterministic but is now 
redefined to be non-deterministic. Its callers may have to be recompiled."
                 predicator world))))


;;; Functions that emit code to construct terms at run time come in several 
;;; flavors...

;; Courtesy IO: SRC; READ.LISP
(DEFUN BACKQUOTIFY-1 (FLAG THING)
       (COND ((OR (EQ FLAG SI:**BACKQUOTE-/,-FLAG**)
                  (MEMQ FLAG '(T NIL)))
              THING)
             ((EQ FLAG 'QUOTE)
              (LIST 'QUOTE THING))
             ((EQ FLAG 'LIST*)
              (COND ((NULL (CDDR THING)) `(prolog-cons ,@thing))
                    (t `(prolog-list* ,@thing))))
             ((EQ FLAG 'LIST)
              `(prolog-list ,@thing))
             ((EQ FLAG 'CONS) `(prolog-cons ,@thing))
             (T (cons flag thing))))

(defun mapterm (vhook target)
  (si:%bind (locf #'si:backquotify-1) #'backquotify-1) ;;Please, forgive me
  (multiple-value-bind (flag thing) (si:backquotify (mapterm-1 vhook target))
    (backquotify-1 flag thing)))

(defun mapterm-1 (vhook x)
  (cond ((value-cell-p x)
	 (cons SI:**BACKQUOTE-/,-FLAG** (funcall vhook x)))
        ((atom x) x)
        (t (cons (mapterm-1 vhook (car x)) (mapterm-1 vhook (cdr x))))))

(defun constructor (target &optional must-dereference)
  (cond ((and (value-cell-p target) must-dereference)
	 (value-cell-access-form target))
        (t (mapterm #'VALUE-CELL-LOCAL-REF target))))

(defun no-dereference (x)
  (cond ((and (consp x) (eq (car x) '%dereference)) (cadr x)) (t x)))

(defun copying-constructor (term)
  (mapterm #'(lambda (x) `(copy-term-1 ,(value-cell-access-form x))) term))


; This way of doing it really screws lazy bags...
; Usage: (progn ,(relocate-body) ...)
;(defun relocate-body ()
;  (AND *VARIABLES-ALIST*
;       `(let ((*variables-alist* ()))
;	  (setq ,@(mapcan #'(lambda (pair)
;			      `(,(constructor (cdr pair))
;				(copy-term-1 ,(constructor (car pair) t))))
;			  *variables-alist*)))))

; Usage: (let* ,(relocate-body) ...)
(defun relocate-body ()
  (AND *VARIABLES-ALIST*
       `((*variables-alist* nil)
	 ,@(mapcar #'(lambda (pair)
		       `(,(constructor (cdr pair))
			 (copy-term-1 ,(constructor (car pair) t))))
		   *variables-alist*))))

(defun relocate (term)
  (cond ((compile-time-void-p term) term)
	((value-cell-p term)
	 (cond ((assq term *variables-alist*) (cdr (assq term *variables-alist*)))
	       (t (push (cons term (compiler-cell)) *variables-alist*)
		  (cdar *variables-alist*))))
	((atom term) term)
	(t (cons (relocate (car term)) (relocate (cdr term))))))
