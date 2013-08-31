;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; Options: ((World Eager)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;This implements bags and sets as seperate parallel processes

(defflavor hurried (process value status inferiors constructor) (prolog-flavor)
 :initable-instance-variables
 :gettable-instance-variables
 :settable-instance-variables)

(defun create-prolog-process (name function &rest arguments)
  (si:%bind (locf #'coroutine-closure-function) #'prolog-process-internal)
  (with-trail (allocate-a-trail)
    (let* ((process
	     (make-instance-in-area-and-initialize *prolog-work-area* 'si:process
	      ':name name
	      ':stack-group
	      (allocate-a-coroutine
		function (first arguments) (copylist (rest1 arguments) *prolog-work-area*))
	      ':priority -1 ;;lower than the Lisp listener
	      ;;(sub1 (funcall current-process ':priority))
	      )))
      (send process ':pre-enable))))

si:
(defmethod (process :pre-enable) ()
  (without-interrupts
    (setq RUN-whostate "Hurrying")
    (set-process-wait self #'true ()))
  self)

(defun prolog-process-internal #.*variables-shared-between-top-level-stack-groups*
  (establish-condition-handlers
    (catch-error-restart ((sys:abort error) "Terminate and free process ~A."
			  (send current-process ':name))
      (with-trail *trail-array* (lexpr-funcall function continuation arglist))))
  (send current-process ':kill))

(defmethod (hurried :add-inferior) (inferior)
  (push inferior inferiors))

(defsubst wait-for-hurried-value (hurried-value)
  (process-wait "Eager value" #'not-hurried hurried-value))

(defun not-hurried (hurried-value)
  (neq (send hurried-value ':status) ':running))

(defmethod (hurried :ordinary-term) ()
  (selectq status
    (:finished value)
    (:running (wait-for-hurried-value self)
              (send self ':ordinary-term))
    (:stopped (cond ((variable-boundp value) value)
                    (t (values self t))))))

(defun hurried-query-user-help (query-io &rest ignore)
  (format
    query-io
    "~%Type /"y/" to wait for the computation to finish,
Type /"n/" to continue,
Type /"p/" to wait for the hurried computation and any embedded ones.
Or type /"f/" to flush the process running the computation."))

(defmethod (hurried :query-user) ()
 (selectq status
   ((:finished :stopped) 'yes)
   (otherwise
    (let ((reply
            (fquery '(:choices
                       (((yes "Yes") #/y)
                        ((no "No") #/n)
                        ((proceed "Proceed") #/p)
                        ((flush "Flush Process") #/f))
                       :help-function
		       hurried-query-user-help)
                    "~%There is a unfinished computation, should I wait for it?  "
                    )))
      (selectq reply
        ((yes proceed) (wait-for-hurried-value self) reply)
        (flush (send process ':flush) 'no)
        (no reply))))))

(defmethod (hurried :kill-process) ()
  ;;have to be careful here that it doesn't change in the middle of this
  (without-interrupts
    (without-interrupts
;     #+SYMBOLICS
      (progn (si:process-disable process)
	     (si:process-all-processes process nil))
;     #-symbolics
;     (send process ':kill)
     (setq status ':stopped)
     (mapc #'(lambda (inferior) (send inferior ':kill-process))
	   inferiors))))

(defmethod (hurried :unify) (other)
  (selectq status
    (:finished (unify value other))
    (:running (wait-for-hurried-value self)
              (send self ':unify other))))

(defvar *hurried-value* ())

(defun next-eager-bag-element ()
  (send *hurried-value* ':new-answer))

(defun next-eager-set-element ()
  (send *hurried-value* ':new-unique-answer))

(defmethod (hurried :new-answer) () 
  (setq value
        (prolog-cons
	  (invoke constructor)
	  (setq *hurried-value*
		(make-instance-in-area *prolog-work-area* 'hurried
		  ':status ':running
		  ':inferiors inferiors
		  ':constructor constructor
		  ':process process))))
  (setq status ':finished)
  nil)

(defvar *set-so-far*)

(defmethod (hurried :new-unique-answer) ()
  (let ((new-element (invoke constructor)))
    (cond ((not (mem 'identical-p new-element *set-so-far*))
           (push new-element *set-so-far*)
           (setq value
                 (prolog-cons
                   new-element
                   (setq *hurried-value*
                         (make-instance-in-area *prolog-work-area* 'hurried
                           ':status ':running
                           ':inferiors inferiors
                           ':constructor constructor
                           ':process process))))
           (setq status ':finished)))
    nil))

(defun make-eager-collection (predications-code constructor)
  (let* ((collection
           (make-instance-in-area *prolog-work-area* 'hurried
             ':status ':running
             ':constructor constructor
             ':inferiors nil))
         (creator *hurried-value*)
         ;;(*hurried-value* collection)
         ;;(*set-so-far* ())
         (process (create-prolog-process "Eager Collection"
                                         #'eager-collection-top-level
					 ;;(closure '(*hurried-value* *set-so-far*)
                                         ;;         #'eager-collection-top-level)
                                         predications-code
					 collection
					 ())))
    (send collection ':set-process process)
    (remind collection ':kill-process)
    (cond (creator (send creator ':add-inferior collection)))
    (process-enable process)
    collection))

(defun eager-collection-top-level (predications-code *hurried-value* *set-so-far*)
  (invoke predications-code)
  (without-interrupts 
    (send *hurried-value* ':set-value nil)
    (send *hurried-value* ':set-status ':finished))
  nil)

(define-predicate wait
  (:options
     (:argument-list (+sixtieths-of-a-second))
     (:documentation
       "the process running this predicate waits +SIXTIETHS-OF-A-SECOND."))
  ((wait ?sixtieths-of-a-second)
   (lisp-command (process-sleep '?sixtieths-of-a-second))))

(define-predicate await
  (:options
     (:argument-list (+predication))
     (:documentation
       "the process running this predicate waits until PREDICATION is true."))
  ((await ?predication)
   (lisp-command
    (process-wait "Await" 'await-1 '?predication
	*trail-array* *prolog-work-area* *vector*)
    )))

(defun await-1 (predication
		*trail-array* *prolog-work-area* *vector*)
  (with-trail *trail-array*
	      (funcall (current-entrypoint 'can-prove)
		       (continuation (true))
		       predication)))

(define-predicate eager-bag-of
  (:options (:compile-method :intrinsic compile-lazy-or-eager-collection)
            (:deterministic :always)
            (:argument-list (bag term &rest +predications))
            (:documentation
              "Unifies BAG with instantiations of TERM in proofs of +PREDICATIONS.
 The BAG is computed in a seperate parallel process"))
  ((eager-bag-of ?bag ?term . ?predications)
   (eager-bag-of ?bag ?term (and . ?predications))))

(define-predicate eager-set-of
  (:options (:compile-method :intrinsic compile-lazy-or-eager-collection)
            (:deterministic :always)
            (:argument-list (set term &rest +predications))
            (:documentation
              "Unifies SET with unique instantiations of TERM in proofs of +PREDICATIONS.
 The SET is computed in a seperate parallel process."))
  ((eager-set-of ?set ?term . ?predications)
   (eager-set-of ?set ?term (and . ?predications))))

(define-predicate faster
  (:options
     (:argument-list (x y))
     (:documentation
       "if X is a hurried value that is still running and Y is not then this fails,
 if X is not hurried this succeeds, 
 if both are hurried then it waits for one to complete."))
  ((faster ?x ?y) (lisp-predicate (faster-value '?x '?y))))

(deffun faster-value (x y)
  (cond ((or (not (typep x 'hurried)) (neq (send x ':status) ':running)) t)
        ((or (not (typep y 'hurried)) (neq (send y ':status) ':running)) nil)
        (t (process-wait "Race" #'not-both-running x y)
           (faster-value x y))))

(defun not-both-running (x y)
  (or (neq (send x ':status) ':running)
      (neq (send y ':status) ':running)))

(define-predicate collect
  ((collect ?collection ?term ?predication :lazy)
   (lazy-bag-of ?collection ?term ?predication))
  ((collect ?collection ?term ?predication :sequential)
   (bag-of ?collection ?term ?predication))
  ((collect ?collection ?term ?predication :eager)
   (eager-bag-of ?collection ?term ?predication)))
