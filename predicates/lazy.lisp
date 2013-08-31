;;; -*- Mode: Lisp; Package: Prolog; Base: 10; Options: ((World System)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;; Part of LM-Prolog that supports lazy collections.

(defflavor lazy-collection (term lazy-list constructor)
	   (prolog-flavor)
  :gettable-instance-variables
  :initable-instance-variables)

(defun lazy-query-user-help (query-io &rest ignore)
  (format query-io
	  "~%Type /"y/" to find the next element of the collection.
Type /"n/" to leave it alone.
Or type /"p/" to find all the elements of the collection."))

(defmethod (lazy-collection :query-user) ()
 (cond ((variable-boundp term) 'yes)
       (t (fquery '(:choices (((yes "Yes") #/y)
			      ((no "No") #/n)
			      ((proceed "Proceed") #/p))
			     :help-function
			     lazy-query-user-help)
		  "~%There is a lazy collection, should I run it? "))))

(defun invoke-then-untrail (cont)
  (let ((mark *trail*))
    (or (invoke cont) (untrail mark) nil)))
	   

(defun lazy-collection-initial-stream (type predications-code constructor)
  (with-trail (allocate-a-trail)
    (let* ((coroutine
	    #-LEXICAL (allocate-a-coroutine
			(first predications-code)
			(second predications-code)
			(rest2 predications-code))
	    #+LEXICAL (allocate-a-coroutine
			#'invoke-then-untrail predications-code ()))
	   (RESUMER (continuation (funcall #'resume coroutine))))
      (selectq type
	(lazy-bag
	 (make-instance-in-area *prolog-work-area* type
	  ':lazy-list RESUMER
	  ':constructor constructor))
	(lazy-set
	 (make-instance-in-area *prolog-work-area* type
	  ':lazy-list RESUMER
	  ':constructor constructor
	  ':list-so-far ()))))))

;;(defmethod (lazy-collection :unify) (other-term)
;;  ;;should this check
;;  ;;(or (null term) (consp term) (typep term 'prolog-flavor)) first ??
;;  (UNIFY (send self ':ordinary-term) other-term))

(defflavor lazy-bag () (lazy-collection)
  :initable-instance-variables)

(defmethod (lazy-bag :ordinary-term) ()
  (cond ((variable-boundp term) term)
	((null (setq lazy-list (invoke lazy-list))) (setq term ()))
	(t (setq term
		 (prolog-cons
		   (invoke constructor)
		   (make-instance-in-area *prolog-work-area* 'lazy-bag
		    ':lazy-list lazy-list ':constructor constructor))))))

(defflavor lazy-set (list-so-far) (lazy-collection)
  :initable-instance-variables)

(defmethod (lazy-set :ordinary-term) ()
  (cond ((variable-boundp term) term)
	((null (setq lazy-list (invoke lazy-list))) (setq term ()))
	(t (let ((element (invoke constructor)))
	     (cond ((mem 'identical-p element list-so-far)
		    (send self ':ordinary-term))
		   (t (setq term
			    (prolog-cons
			      element
			      (make-instance-in-area *prolog-work-area* 'lazy-set
			       ':lazy-list lazy-list
			       ':constructor constructor
			       ':list-so-far
			       (prolog-cons element list-so-far))))))))))

(eval-when (compile eval load)

(defmacro push-for-set (item access)
  `(let ((item ,item))
     (cond ((not (mem 'identical-p item ,access))
	    (push-in-area item ,access *prolog-work-area*)))))

(defmacro push-for-bag (item access)
  `(push-in-area ,item ,access *prolog-work-area*))

(defun compile-collection
       (if then bag-term term-term &rest predications
	&aux (det (det-conjuncts-p predications t))
	     (DEEP (DEEP-BACKTRACK-P PREDICATIONS NIL)))
  (cond ((NOT (OR (NULL BAG-TERM) (CONSP BAG-TERM) (VALUE-CELL-P BAG-TERM)))
	 (PROLOG-WARN ':ATOMIC-COLLECTION ':IMPLAUSIBLE
		      "~a can't be a collection"
		      BAG-TERM))
	((AND DET (> (length (cons 0 bag-term)) 2))
	 (prolog-warn ':determinate-collection-too-long
		      ':implausible
		      "~a is deterministic, a collection of it is at most one long"
		      (caar predications))))
  (values
   (cond ((compile-time-void-p bag-term)
	  `(let ,(AND DEEP `((mark *trail*)))
	     ,(conjunction predications '(false) ())
	     ,@(AND DEEP `((untrail mark)))
	     ,if))
	 ((AND DET
	       (CONSP BAG-TERM)
	       (COMPILE-TIME-VOID-P (CAR BAG-TERM)))
	  `(let ,(AND DEEP `((mark *trail*)))
	     (cond (,(conjunction predications '(true) ())
		    ,@(AND DEEP `((untrail mark)))
		    (AND ,(compile-unification `() (cdr bag-term)) ,IF)))))
	 (DET
	  `(let ,(AND DEEP `((mark *trail*)))
	     (cond (,(conjunction predications '(true) ())
		    (LET* (*VARIABLES-ALIST*
			   (copy ,(copying-constructor term-term)))
		      ,@(AND DEEP `((untrail mark)))
		      (AND ,(compile-unification `(prolog-list copy) bag-term)
			   ,IF))))))
	 (t (let ((bag (compiler-gensym)))
	      `(let (,@(AND DEEP `((mark *trail*))) (,bag (prolog-list ())))
		 ,(conjunction predications
		   `(let ((*variables-alist* ()))
		      (,(selectq (car *predication*)
			  (bag-of `push-for-bag)
			  (set-of `push-for-set))
		       ,(copying-constructor term-term)
		       (car ,bag))
		      nil)
		   ())
		 ,@(AND DEEP `((untrail mark)))
		 (and ,(compile-unification `(nreverse (car ,bag)) bag-term)
		      ,if)))))
   then))

(defun compile-lazy-or-eager-collection
       (if then bag-term term-term
	&rest predications
	&aux (det (det-conjuncts-p predications t))
	     (DEEP (DEEP-BACKTRACK-P PREDICATIONS NIL)))
  (COND ((NOT (OR (NULL BAG-TERM) (CONSP BAG-TERM) (VALUE-CELL-P BAG-TERM)))
	 (PROLOG-WARN ':ATOMIC-COLLECTION ':IMPLAUSIBLE
		      "~a can't be a collection"
		      BAG-TERM))
	((AND det (> (length (cons 0 bag-term)) 2))
	 (prolog-warn ':determinate-collection-too-long
		      ':implausible
		      "~a is deterministic, a collection of it is at most one long"
		      (caar predications)))
	((COMPILE-TIME-VOID-P BAG-TERM)
	 (prolog-warn ':collection-mistakenly-non-sequential ':implausible
		      "~a with an anonymous variable as its first
argument is a no-op, you may want an ordinary collection"
		      (car *predication*))))
  (values
    (cond ((COMPILE-TIME-VOID-P bag-term)
	   if)
	 ((null bag-term)
	   `(let ,(AND DEEP `((mark *trail*)))
	      (cond ((not ,(conjunction predications '(true) ()))
		     ,@(AND DEEP `((untrail mark)))
		     ,if))))
	  (DET
	   (LEXPR-FUNCALL #'COMPILE-COLLECTION IF THEN BAG-TERM TERM-TERM PREDICATIONS))
	  ((and (consp bag-term)
		(COMPILE-TIME-VOID-P (CAR BAG-TERM))
		(COMPILE-TIME-VOID-P (CDR BAG-TERM)))
	   `(let ,(AND DEEP `((mark *trail*)))
	      (cond (,(conjunction predications '(true) ())
		     ,@(AND DEEP `((untrail mark)))
		     ,IF))))
	  ((and (consp bag-term) (COMPILE-TIME-VOID-P (CDR BAG-TERM)))
	   `(let ,(AND DEEP `((mark *trail*)))
	      (cond (,(conjunction predications '(true) ())
		     (LET* (*VARIABLES-ALIST*
			    (copy ,(copying-constructor term-term)))
		       ,@(AND DEEP `((untrail mark)))
		       (AND ,(compile-unification `COPY (CAR BAG-TERM)) ,IF))))))
	  ((and (consp bag-term)
		(or (null (cdr (last bag-term)))
		    (compile-time-void-p (cdr (last bag-term)))))
	   (let* ((bag (compiler-gensym))
		  (*variables-alist* ())
		  (predications-1 (relocate predications))
		  (term-term-1 (relocate term-term))
		  (throw-after
		    (cond ((compile-time-void-p (cdr (last bag-term)))
			   (length bag-term))
			  (t -1))))
	     `(let* (,@(relocate-body)
		     (,bag
		      (make-instance-in-area-and-initialize
			*prolog-work-area*
			',(selectq (car *predication*)
			    ((lazy-bag-of eager-bag-of) 'semilazy-bag)
			    ((lazy-set-of eager-set-of) 'semilazy-set))
			':throw-after ,throw-after
			',(selectq (car *predication*)
			    ((lazy-bag-of eager-bag-of) `:bag-pointer)
			    ((lazy-set-of eager-set-of) `:set-pointer))
			,(constructor bag-term t)
			':constructor
			(continuation
			  (let ((*variables-alist* ()))
			    ,(copying-constructor term-term-1))))))
		(and
		  (*catch ,bag
		    (with-trail (allocate-a-trail)
		      (cond ((not ,(conjunction predications-1
						`(send ,bag ':next-proof) ()))
			     (send ,bag ':end)))))
		  ,if))))
	  (t `(let ((the-bag
		      (,(cdr (assq (car *predication*)
				   '((lazy-bag-of . general-lazy-bag)
				     (lazy-set-of . general-lazy-set)
				     (eager-bag-of . general-eager-bag)
				     (eager-set-of . general-eager-set))))
		       ,(constructor term-term t)
		       ,(constructor predications t))))
		(and ,(compile-unification 'the-bag bag-term) ,if)))

;	  (t (let* ((*variables-alist* ())
;		    (predications-1 (relocate predications))
;		    (term-term-1 (relocate term-term))
;		    (constructor
;		      `(continuation
;			 (let ((*variables-alist* ()))
;			   ,(copying-constructor term-term-1)))))
;	       `(let* (,@(relocate-body)
;		       (the-bag
;			,(selectq (car *predication*)
;			   (lazy-bag-of
;			    `(lazy-collection-initial-stream
;			       'lazy-bag
;			       (continuation
;				 ,(conjunction predications-1
;					       '(stack-group-return t)
;					       ()))
;			       ,constructor))
;			   (lazy-set-of
;			    `(lazy-collection-initial-stream
;			       'lazy-set
;			       (continuation
;				 ,(conjunction predications-1
;					       '(stack-group-return t)
;					       ()))
;			       ,constructor))
;			   (eager-bag-of
;			    `(make-eager-collection
;			       (continuation
;				 ,(conjunction predications-1
;					       '(next-eager-bag-element)
;					       ()))
;			       ,constructor))
;			   (eager-set-of
;			    `(make-eager-collection
;			       (continuation
;				 ,(conjunction predications-1
;					       '(next-eager-set-element)
;					       ()))
;			       ,constructor)))))
;		  (and ,(compile-unification 'the-bag bag-term) ,if))))
	  )
    then))


)
;not really a Prolog flavor - never used as a term
(defflavor semilazy-bag
	   (bag-pointer so-far constructor trail throw-after) ()
  :initable-instance-variables)

(defflavor semilazy-set
	   (set-pointer set-so-far constructor trail throw-after) ()
  :initable-instance-variables)

(defmethod (semilazy-bag :init) (ignore)
  (setq trail *trail-array* so-far 0))

(defmethod (semilazy-set :init) (ignore)
  (setq trail *trail-array* set-so-far ()))

(defmethod (semilazy-bag :next-proof) ()
  ;;if this returns T the semilazy-bag fails!
  (setq bag-pointer (%dereference bag-pointer))
  (let* ((copy (invoke constructor)))
    (incf so-far)
    (cond ((cond ((consp bag-pointer)
		  (with-trail trail
		    (UNIFY (pop bag-pointer) copy)))
		 (t (with-trail trail
		      (UNIFY
			bag-pointer
			(prolog-cons copy (setq bag-pointer (%cell0)))))))
	   (cond ((= throw-after so-far) (*throw self t))))
	  (t t))))

(defmethod (semilazy-set :next-proof) ()
  ;;if this returns T the semilazy-bag fails!
  (setq set-pointer (%dereference set-pointer))
  (let* ((copy (invoke constructor)))
    (cond ((mem 'identical-p copy set-so-far) nil)
	  (t (setq set-so-far (prolog-cons copy set-so-far))
	     (cond ((cond ((consp set-pointer)
			   (with-trail trail
			     (UNIFY (pop set-pointer) copy)))
			  (t (with-trail trail
			       (UNIFY
				 set-pointer
				 (prolog-cons
				   copy (setq set-pointer (%cell0)))))))
		    (cond ((= throw-after (length set-so-far))
			   (*throw self t))))
		   (t t))))))

(defmethod (semilazy-bag :end) ()
  (with-trail trail (UNIFY (%dereference bag-pointer) ())))

(defmethod (semilazy-set :end) ()
  (with-trail trail (UNIFY (%dereference set-pointer) ())))

(define-predicate bag-of
  (:options
     (:argument-list (bag term &rest +predications))
     (:documentation
       "Unifies BAG with instantiations of TERM in proofs of +PREDICATIONS.")
     (:compile-method :intrinsic compile-collection)
     (:deterministic :always))
  ((bag-of ?bag ?term . ?predications) (bag-of ?bag ?term (and . ?predications))))

(define-predicate set-of
  (:options
     (:argument-list (set term &rest +predications))
     (:documentation
      "Unifies SET with unique instantiations of TERM in proofs of +PREDICATIONS.")
     (:compile-method :intrinsic compile-collection)
     (:deterministic :always))
  ((set-of ?set ?term . ?predications) (set-of ?set ?term (and . ?predications))))

(define-predicate lazy-bag-of
  (:options (:compile-method :intrinsic compile-lazy-or-eager-collection)
	    (:argument-list (bag term &rest +predications))
	    (:documentation
	      "Unifies BAG with instantiations of TERM in proofs of +PREDICATIONS.
 The BAG is computed in a demand-driven fashion.")
	    (:deterministic :always))
  ((lazy-bag-of ?bag ?term . ?predications)
   (lazy-bag-of ?bag ?term (and . ?predications))))

(define-predicate lazy-set-of
  (:options (:compile-method :intrinsic compile-lazy-or-eager-collection)
	    (:deterministic :always)
	    (:argument-list (set term &rest +predications))
	    (:documentation
	      "Unifies SET with unique instantiations of TERM in proofs of +PREDICATIONS.
 The SET is computed in a demand-driven fashion."))
  ((lazy-set-of ?set ?term . ?predications)
   (lazy-set-of ?set ?term (and . ?predications))))

;;;I give up!  The semantics of lexical scoping + coroutines + tail recursion opt. 
;;;is beyond me.  Thus full lazy or eager bags call these.

(defun general-lazy-bag (term conjunction)
  (let ((term-conj (copy-term (prolog-cons term conjunction)))
        (cont-1 (continuation (funcall 'stack-group-return t))))
    (lazy-collection-initial-stream
      'lazy-bag
      (continuation (funcall 'prove-conjunction-if-need-be (cdr term-conj) cont-1))
      (continuation (funcall 'copy-term (car term-conj))))))


(defun general-lazy-set (term conjunction)
  (let ((term-conj (copy-term (prolog-cons term conjunction)))
        (cont-1 (continuation (funcall 'stack-group-return t))))
    (lazy-collection-initial-stream
      'lazy-set
      (continuation (funcall 'prove-conjunction-if-need-be (cdr term-conj) cont-1))
      (continuation (funcall 'copy-term (car term-conj))))))


(defun general-eager-bag (term conjunction)
  (let ((term-conj (copy-term (prolog-cons term conjunction)))
	(cont-1 (continuation (funcall 'next-eager-bag-element))))
    (make-eager-collection
      (continuation (funcall 'prove-conjunction-if-need-be (cdr term-conj) cont-1))
      (continuation (funcall 'copy-term (car term-conj))))))


(defun general-eager-set (term conjunction)
  (let ((term-conj (copy-term (prolog-cons term conjunction)))
	(cont-1 (continuation (funcall 'next-eager-set-element))))
    (make-eager-collection
      (continuation (funcall 'prove-conjunction-if-need-be (cdr term-conj) cont-1))
      (continuation (funcall 'copy-term (car term-conj))))))


(compile-flavor-methods lazy-collection lazy-bag lazy-set semilazy-bag semilazy-set)
