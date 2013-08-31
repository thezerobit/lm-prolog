;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; Options: ((WORLD SYSTEM) (DETERMINISTIC ALWAYS)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;this implements a variant of Marsielle's Prolog II's geler in LM-Prolog
;;this version is deterministic

;;See LMP:LIBRARY;ARITHMETIC LISP and GRAPHICS-DEMOS LISP for examples of its use.

;;Here is some support for deterministic proofs.

(defsubst prove-once-if-need-be (predications)
  (or (null predications) (prove-once predications)))

(deffun prove-once (predications)
  (let* ((predication (first predications))
         (interpreter-slot
           (definition-interpreter-slot (current-definition (first predication)))))
    (cond ((null (rest1 predications))
           (prove predication interpreter-slot (continuation (true))))
	  ((interpreter-slot-deterministic interpreter-slot)
	   (cond ((prove predication interpreter-slot (continuation (true)))
		  (prove-once (rest1 predications)))))
	  (t (prove predication
		    interpreter-slot
		    (continuation (funcall #'prove-once (rest1 predications))))))))

(eval-when (compile eval load)
(defflavor constraint
	   (cell				;A value cell whose contents is
						;self (for unbound)
						;another constraint (bound or unbound)
						;or a term (bound).

	    constraints				;The constraints to be satisfied.
						;A list of predication.
	    )
	   (prolog-flavor)
  :initable-instance-variables
  :gettable-instance-variables
  :settable-instance-variables))

(defmethod (constraint :unify) (other)
  (cond ;;Pass on if we have been forwarded.
        ((neq (contents cell) self)
	 (unify (contents cell) other))
	;;We are not forwarded but other is constrained.
	((typep other 'constraint)
         (let ((others-cell (send other ':cell)))
           (cond ;;Pass on if other has been forwarded. 
		 ;;Other may even have been forwarded to us!
	         ((neq (contents others-cell) other)
		  (unify self (contents others-cell)))
		 ;;Otherwise, forward self to the other, and combine the constraints.
		 (t (remind self ':reset-cell)
		    (unify cell others-cell)
		    (send other ':add-constraints constraints)))))
	;;We are plainly constrained and the other is not constrained.
        (t (remind self ':reset-cell)
	   (unify cell other)
	   (with-new-*vector* (prove-once-if-need-be constraints)))))

(defmethod (constraint :add-constraints) (predications)
  (cond ;;Pass on if we have been forwarded.
        ((neq (contents cell) self)
	 (constrain-variable-1 (contents cell) predications))
	((with-new-*vector*
	   (let* ((combined-constraints
		    (combine-constraints constraints predications)))
	     (selectq combined-constraints
	       (:fail nil)
	       (:invoke (prove-once-if-need-be predications))
	       (t (cond (t
			 (remind self ':set-constraints constraints)
			 (setq constraints combined-constraints)
			 t)))))))))

;;This used to do an IDENTITY-UNION of the constraints.
;;I think that was due to a losing implementation of :THAW.
(defun combine-constraints (constraints-1 constraints-2)
  (let ((both (%cell0)) (mark *trail*))
    (cond ((funcall (current-entrypoint 'combine-constraints)
		    (continuation (true))
		    both constraints-1 constraints-2)
	   (%dereference both))
	  (t (untrail mark) (prolog-append constraints-1 constraints-2)))))


(defmethod (constraint :reset-cell) ()
  (setf (contents cell) self))

(defmethod (constraint :ordinary-term) ()
  ;;This must NOT return self, would cause bad loops in the error-handler.
  (cond ((eq (contents cell) self) cell)	 
	((typep (contents cell) 'prolog-flavor)
	 (send (contents cell) ':ordinary-term))
        (t (contents cell))))

(defvar *absurdity*)

(let ((*prolog-work-area* *structure-area*))
  (setq *absurdity* (make-instance-in-area *prolog-work-area* 'constraint
					   ':cell (%cell0)
					   ':constraints '((false)))))

(rplacd (send *absurdity* ':cell) *absurdity*)

(defmethod (constraint :thaw) (mode)
  (let ((mark *trail*))
    (COND ((send self ':unify (%cell0))
	   (cond ((neq (contents cell) self) (lisp-form-1 (contents cell) mode))
		 (t self)))
	  (T ;;Incompatible constraints that weren't detected until now.
	   (untrail mark) *absurdity*))))

(defmethod (constraint :lisp-form) (mode)
  (cond ((neq (contents cell) self) (lisp-form-1 (contents cell) mode))
	(t
         (selectq mode
	   (:dont-invoke self)
           (:query
            (selectq (send self ':query-user)
              (no self)
              (yes (send self ':thaw mode))
              (proceed (send self ':lisp-form ':invoke))))
	   (t (send self ':thaw mode))))))

(defvar *constraints-being-printed* nil)

(defmethod (constraint :print-self) (stream level escape)
  (cond ((variable-boundp *symbol-table*)
	 (let ((*print-escape* escape)
	       (*print-level* (and *print-level* (- *print-level* level)))
	       (*print-pretty* nil)		;otherwise, bad loop!
	       )
	   (cond
	     ((neq (contents cell) self)	;Is this a possible case?
	      (write (contents cell) ':stream stream))
	     ((memq self *constraints-being-printed*)
	      (write (lisp-form-1 cell ':dont-invoke) ':stream stream))
	     (t (with-stack-list* (*constraints-being-printed* self *constraints-being-printed*)
		  (let ((lisp-constraints (lisp-form-1 constraints ':dont-invoke)))
		    (format stream "#<a ~S such that ~VQ>"
			    (lisp-form-1 cell ':dont-invoke)
			    (cond ((null constraints) '(true))
				  ((cdr constraints) (prolog-cons 'and lisp-constraints))
				  ((car lisp-constraints)))
			    #'write)))))))
	 (t
	   (using-resource (*symbol-table* symbol-table)
	     (using-resource (tr trail 500)
	       (with-trail tr
		 (send self :print-self stream level escape)))))))


(defmethod (constraint :query-user) ()
  (fquery '(:choices (((yes "Yes") #/y)
		      ((no "No") #/n)
		      ((proceed "Proceed") #/p))
		     :help-function
		     (lambda (query-io ignore ignore)
		       (format query-io
			       "~%Type /"y/" to run the constraints.
Type /"n/" to leave it alone.
Or type /"p/" to run the constraints and any that pop up in the process.")))
	  "~%There is a constrained variable, should I run its constraints? "))

(defmethod (constraint :variable-p) ()
  (or (eq (contents cell) self)
      (unbound-variable-p (contents cell))))

;;This was hairier and had the bug that occurences to SELF in CONSTRAINTS weren't preserved.
(DEFMETHOD (CONSTRAINT :COPY) ()
  (COND ((CDR (ASSQ SELF *CONSES-ALIST*)))
	(T (LET ((NEW-CELL (%CELL0)))
	     (WITH-STACK-LIST*
	       (PAIR SELF (MAKE-INSTANCE-IN-AREA *PROLOG-WORK-AREA* 'CONSTRAINT
						 ':CELL NEW-CELL))
	       (WITH-STACK-LIST* (*CONSES-ALIST* PAIR *CONSES-ALIST*)
		 (SETF (CONTENTS NEW-CELL) (COPY-TERM-1 (CONTENTS CELL)))
		 (SEND (CDR PAIR) ':SET-CONSTRAINTS (COPY-TERM-1 CONSTRAINTS))
		 (CDR PAIR)))))))

(defun constrain-variable-1 (variable predications)
  (cond ((typep variable 'constraint)
	 (send variable ':add-constraints predications))
        (t (unify variable
                  (make-instance-in-area
                    *prolog-work-area*
                    'constraint
                    ':cell variable
		    ':constraints predications)))))

(define-predicate constrain
  (:options
    (:argument-list (variable predication))
    (:documentation
      "postpones the execution of PREDICATION until VARIABLE has been instantiated."))
  ((constrain ?variable ?goal)
   (cases ((variable ?variable)
	   (lisp-predicate (constrain-variable-1 '?variable '(?goal))))
	  (?goal))))

(define-predicate freeze
  (:options
    (:argument-list (predication &optional count))
    (:documentation "postpones the deterministic execution of PREDICATION until
at most COUNT distinct variables are unbound."))
  ((freeze ?goal) (freeze ?goal 0))
  ((freeze ?goal ?n) (lisp-predicate (freeze-function '?goal '?n))))

;This provides mutual exclusion for the above.
(define-predicate thaw
  ((thaw ?goal ?i ?i) ?goal)
  ((thaw ? ? ?)))
  

(define-predicate not
  (:options
    (:compile-method :open)
    (:argument-list (predication))
    (:documentation "postpones the execution of (CANNOT-PROVE PREDICATION) until PREDICATION
 is ground"))
  ((not ?predication)
   (freeze (cannot-prove ?predication))))

(define-predicate 
  (:options
    (:argument-list (x y))
    (:documentation "is true if X and Y do not unify."))
  (( ?x ?y) (lisp-predicate (-function '?x '?y))))

(defun freeze-function (goal count)
  (let ((vars (n-variables-in goal (1+ count))))
    (cond ((null vars)
	   (with-stack-list (goals goal) (prove-once goals)))
	  ((null (cdr vars))
	   (constrain-variable-1
	     (car vars)
	     (prolog-list (prolog-list 'freeze goal count))))
	   ((let ((goal (prolog-list 'freeze goal count))
		  (mutex (%cell0)))
	      (do ((vas vars (cdr vas))
		   (i 0 (1+ i)))
		  ((null vas) t)
		(constrain-variable-1
		  (car vas)
		  (prolog-list (prolog-list 'thaw goal i mutex)))))))))

(defun n-variables-in (term count)
  (*catch 'n-variables-in
    (prog1 nil (n-variables-in-term term count ()))))

(deffun n-variables-in-term (term count sofar)
  (cond ((consp term)
	 (n-variables-in-term (cdr term) count
			      (n-variables-in-term (car term) count sofar)))
	((unbound-variable-p term)
	 (or (memq term sofar)
	     (push-in-area term sofar *prolog-work-area*))
	 (cond ((= count (length sofar)) (*throw 'n-variables-in sofar)))
	 sofar)
	(t sofar)))

(defun -function (x y)
  (multiple-value-bind (id-p some-x some-y)
      (identical-p x y)
    (cond ((not id-p)
	   (and (cond ((unbound-variable-p some-x)
		       (constrain-variable-1 some-x (prolog-list (prolog-list ' x y))))
		      (t t))
		(cond ((unbound-variable-p some-y)
		       (constrain-variable-1 some-y (prolog-list (prolog-list ' x y))))
		      (t t)))))))

(defun prolog-append (list1 list2)
  (nconc (copylist* list1 *prolog-work-area*) list2))

(define-predicate combine-constraints
  ((combine-constraints :fail ?constraints ?)
   (member ( ?a ?b) ?constraints)
   (identical ?a ?b))
  ((combine-constraints :fail ? ?constraints)
   (member ( ?a ?b) ?constraints)
   (identical ?a ?b))
  ;;to be general this should really do a sort of UNION
  ((combine-constraints ?both (?constraint-1) (?constraint-2))
   (or (*combine-constraints* ?both ?constraint-1 ?constraint-2)
       (*combine-constraints* ?both ?constraint-2 ?constraint-1))))

(define-predicate *combine-constraints*
  (:options (:type :dynamic)))

;;They really should be part of the standard system...
(globalize 'freeze ':pglobal)
(globalize 'constrain ':pglobal)
(globalize 'combine-constraints ':pglobal)

