;;; -*- Mode: Lisp; Package: PROLOG; Base: 10.; Options: ((World System)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;this file contains the interface to Lisp and control primitives of LM-Prolog

(define-predicate lisp-predicate
  (:options (:compile-method :intrinsic compile-lisp-predicate)
	    (:deterministic :always)
	    (:argument-list (+form &optional +conversion-mode))
	    (:documentation "succeeds if +FORM evaluates to non-nil."))
  ((lisp-predicate ?r) (lisp-predicate ?r))
  ((lisp-predicate ?r ?mode) (lisp-predicate ?r ?mode)))

(define-predicate lisp-command
  (:options (:compile-method :intrinsic compile-lisp-command)
	    (:deterministic :always)
	    (:argument-list (+form &optional +conversion-mode))
	    (:documentation "evaluates +FORM.  Always succeeds."))
  ((lisp-command ?r) (lisp-command ?r))
  ((lisp-command ?r ?mode) (lisp-command ?r ?mode)))

(define-predicate lisp-value
  (:options (:compile-method :intrinsic compile-lisp-value)
	    (:deterministic :always)
	    (:argument-list (value +form &optional +conversion-mode))
	    (:documentation "unifies VALUE with the result of evaluating +FORM."))
  ((lisp-value ?X ?Y) (lisp-value ?X ?Y))
  ((lisp-value ?X ?Y ?mode) (lisp-value ?X ?Y ?mode)))

(define-predicate *make-true*
  :(options (type dynamic)))

(define-predicate *make-true*
  :(options (if-old-definition keep))
  (:setf-1
    (*make-true* (lisp-value ?value ?access))
    (lisp-command (eval '(setf ?access '?value))))
  (:setf-2
    (*make-true* (lisp-value ?value ?access ?mode))
    (lisp-command (eval '(setf ?access '?value)) ?mode)))

(define-predicate *current-value-finder*
  :(options (type dynamic)))

(define-predicate *current-value-finder*
  :(options (if-old-definition keep))
  (:lisp-value-finder-1
    (*current-value-finder*
      (lisp-value ? ?form) (lisp-value ? ?form)))
  (:lisp-value-finder-2
    (*current-value-finder*
      (lisp-value ? ?form ?mode) (lisp-value ? ?form ?mode))))

(define-predicate =
  (:options (:compile-method :open)
	    (:argument-list (x y))
	    (:documentation "unifies X with Y."))
  ((= ?x ?x)))

(define-predicate or
  (:options (:compile-method :intrinsic compile-or-internal)
	    (:argument-list (&rest predications))
	    (:documentation "tries PREDICATIONS, one at a time."))
  ((or ?x . ?) ?x)
  ((or ? . ?x) (or . ?x)))


(define-predicate cut
  (:options
    (:argument-list ())
    (:documentation
      "is equivalent to (or (true) (the-predicate-i/'m-inside-of-is-false)).")
    (:compile-method :intrinsic compile-cut))
  ((cut) (lisp-command (*throw *cut-tag* (invoke .continuation.)))))

(define-predicate and
  (:options (:compile-method :intrinsic compile-and-internal)
	    (:argument-list (&rest +predications))
	    (:documentation "proves the conjunction of +PREDICATIONS."))
  ((and . ?predications) . ?predications))

(define-predicate *make-true*
  (:options (:if-old-definition :keep))
  (:make-true-conjunction
    (*make-true* (and ?predication . ?more))
    (make-true ?predication)
    (make-true (and . ?more))))

(define-predicate *current-value-finder*
  (:options (:if-old-definition :keep))
  (:and-value-finder
    (*current-value-finder* (and . ?finders) (and . ?predications))
    (bag-of ?finders
	    ?finder
	    (member ?predication ?predications)
	    (*current-value-finder* ?finder ?predication))))

(define-predicate fail
  (:options (:compile-method :open)
	    (:documentation "is always false.")))

(define-predicate false
  (:options (:compile-method :open)
	    (:documentation "is always false.")))

(define-predicate true
  (:options (:compile-method :open)
	    (:documentation "is always true."))
  ((true)))

(define-predicate comment
  (:options (:compile-method :open)
	    (:documentation "is a no-op, works as true."))
  ((comment . ?)))

(define-predicate call 
 (:options
   (:compile-method :intrinsic compile-call)
   (:argument-list (+predication &optional +world))
   (:documentation
     "proves +PREDICATION. Definition can be fetched from specific +WORLD."))
  ((call ?predication) (call ?predication))
  ((call ?predication ?world) (call ?predication ?world)))

(define-predicate cannot-prove
  (:options
    (:compile-method :open)
    (:argument-list (&rest +predications))
    (:documentation
      "succeeds if the system cannot prove the conjunction of the +PREDICATIONS."))
  ((cannot-prove . ?predications) (lazy-bag-of () () (and . ?predications))))

;;(define-predicate repeat
;;  ((repeat ?n) ( ?n 0) (sum ?n-1 ?n -1) (or (true) (repeat ?n-1))))

;;the following is a hand-coded version of the above

(define-predicate repeat
  (:options (:argument-list (&optional +times))
	    (:documentation "succeeds +TIMES or infinity times.")
	    (:compile-method :intrinsic compile-repeat))
	((repeat) (repeat))
	((repeat ?N) (repeat ?N)))

(define-predicate unwind-protect
  (:options
    (:compile-method :intrinsic unwind-protect-emitter)
    (:argument-list (+predication &rest +undo-predication))
    (:documentation
      "is logically equivalent to (or +PREDICATION (and (and . +UNDO-PREDICATIONS) (false))),
  however it guarantees that +UNDO-PREDICATIONS will be executed
  even in the case of abnormal exit (e.g. via <abort> or lazy collections)."))
  ((unwind-protect ?predication . ?undo-predications)
   (unwind-protect ?predication (and . ?undo-predications))))

#-symbolics
(define-predicate condition-protect
  :(options
    (deterministic always)
    (argument-list (+condition-name +predication &rest +undo-predication))
    (documentation
      "executes +PREDICATION deterministically.
 If during its execution a condition named +CONDITION-NAME is signalled,
 +PREDICATION is aborted and +UNDO-PREDICATIONS are deterministically executed instead.")))

#-symbolics
(defun #.(prolog-db-symbol 'condition-protect ':system 'prover)
  (cont cond-name goal &rest undo-goals)
  (and
   (let ((tag (gensym)))
    (*catch tag
      (condition-bind
	((()
	  #'(lambda (inst name tag undo)
	      (cond ((memq name (send inst ':condition-names))
		     (*throw tag (prove-conjunction-if-need-be undo (continuation (true)))))))
	  (%dereference cond-name) tag (rest-arg-fixup undo-goals)))
	(with-stack-list (goals (%dereference goal))
	  (prove-conjunction goals (continuation (true)))))))
   (invoke cont)))

(define-predicate interrupts
  (:options (:argument-list (on-or-off))
	    (:documentation "ON-OR-OFF is :on or :off when interrupts are on or off."))
  ((interrupts :on) (lisp-value nil inhibit-scheduling-flag))
  ((interrupts :off) (lisp-predicate inhibit-scheduling-flag)))


(define-predicate cases
  (:options (:compile-method :intrinsic cases-emitter)
	    (:argument-list (&rest +cases))
	    (:documentation
	      "is the same as the conjunction of the first case in +CASES whose
 first element is provable."))
  ((cases (?A . ?R) . ?S)
   (cases (?A (and . ?R)) ((cases . ?S)))))

(define-predicate if
  (:options
    (:argument-list (+test +then &rest +else))
    (:documentation
      "is equivalent to (or (and +TEST +THEN) (and (cannot-prove +TEST) . +ELSE).")
    (:compile-method :open))
  ((if ?test ?then . ?else)
   (cases (?test ?then) ((true) . ?else))))

(define-predicate either
  (:options (:compile-method :intrinsic either-emitter)
	    (:argument-list (&rest +predications))
	    (:documentation
	      "is like OR except is happy with the first provable predication."))
  ((either ?predication-1 ?predication-2 . ?more)
   (cases (?predication-1) (?predication-2) ((either . ?more))))
  ((either ?predication) ?predication))

(define-predicate rules
  (:options (:compile-method :intrinsic rules-emitter)
	    (:argument-list (term &rest +rules))
	    (:documentation
	      "is the same as the conjunction of the rest of the first rule whose
 first element unifies with TERM."))
  ((rules ?thing ?clause . ?more-clauses)
   (cases ((= ?clause (?thing . ?conditions)) (and . ?conditions))
	  ((rules ?thing . ?more-clauses)))))

(define-predicate prove-once
  (:options
    (:compile-method :open) ;;since meta-level predicate
    (:argument-list (&rest +predications))
    (:documentation
      "considers only the first proof of the conjunction of +PREDICATIONS."))
  ((prove-once . ?predications) (and . ?predications) (cut)))

(define-predicate can-prove
  (:options (:compile-method :open)
	    (:argument-list (&rest +predications))
	    (:documentation
	      "succeeds if the conjunction of +PREDICATIONS are provable.
 This does NOT create any bindings."))
  ((can-prove . ?predications)
   (lazy-bag-of (? . ?) () (and . ?predications))))

(define-predicate not-=
  (:options (:compile-method :open)
	    (:documentation
	      "succeeds if its arguments don't unify, otherwise fails.
 Note that this fails for (NOT-= ?a ?b) if either ?a or ?b are unbound.")
	    (:argument-list (x y)))
  ((not-= ?x ?y) (cannot-prove (= ?x ?y))))

(define-predicate lisp-type
  (:options
    (:compile-method :open)
    (:argument-list (type term))
    (:documentation
      "fails if TERM is a variable, otherwise unifies TYPE with the type of TERM.
 The type is the same as Lisp's typep."))
  ((lisp-type ?type ?term)
   (lisp-value ?type (type-even-of-prolog-flavors '?term))
   (not-= ?type locative)))

(deffun type-even-of-prolog-flavors (term)
  (cond ((typep term 'prolog-flavor)
	 (type-even-of-prolog-flavors (send term ':ordinary-term)))
	((type-of term))))

(define-predicate let
  (:options
    (:compile-method :intrinsic compile-let)
    (:argument-list (+assumption))
    (:documentation "is an operator upon +assumption:
 it is assumed to be true until backtracking. (See WITH)"))
  ((let ?assumption)
   (cases ((prove-once
	     (*current-value-finder* ?restore-current-value
				     ?assumption))
	   ?restore-current-value
	   (unwind-protect (make-true ?assumption)
			   (make-true ?restore-current-value)))
	  ((assume (?assumption))))))

(define-predicate with
  (:options
    (:compile-method :intrinsic compile-with)
    (:argument-list (+to-make-true &rest +predications))
    (:documentation
      "proves the conjunction of +PREDICATIONS with the predication +TO-MAKE-TRUE
 made true.  (See MAKE-TRUE.)"))
  ((with ?make-true-predication . ?predications)
   (cases ((prove-once
	     (*current-value-finder* ?restore-current-value
				     ?make-true-predication))
	   ?restore-current-value
	   (unwind-protect (make-true ?make-true-predication)
			   (make-true ?restore-current-value))
	   (and . ?predications)
	   (unwind-protect (make-true ?restore-current-value)
			   (make-true ?make-true-predication)))
	  ((generate-symbol ?clause-name clause)
	   (unwind-protect
	     (assert (?clause-name ?make-true-predication))
	     (retract (?clause-name ?make-true-predication)))
	   (and . ?predications)
	   (unwind-protect
	     (retract (?clause-name ?make-true-predication))
	     (assert (?clause-name ?make-true-predication)))))))

(define-predicate variables
  (:options
     (:argument-list (variables &rest +terms))
     (:compile-method :open)
     (:documentation
       "binds VARIABLES to the unbound variables inside of +TERMS."))
  ((variables ?variables . ?terms)
   (lisp-value ?variables (nreverse (variables-in '?terms)))))

;(define-predicate closed-term
;  ((closed-term ?closed ?open)
;   (lazy-bag-of (?closed) ?closed (close ?open) (= ?open ?closed))))

;(define-predicate close
;  ((close ?open-term)
;   (variables ?variables ?open-term)
;   (map generate-unique-name ?variables)))

(define-predicate ground
  (:options (:argument-list (term))
            (:compile-method :open)
            (:documentation "succeeds if there are no unbound variables in TERM."))
  ((ground ?term)
   (lisp-predicate (not (not-ground-p '?term)))))


(define-predicate map
  (:options
     (:argument-list (+predicator &rest +lists))
     (:documentation "applies +PREDICATOR to corresponding elements of +LISTS."))
  ((map ?predicator . ?lists)
   ;;this is logically sufficient but too inefficient for the simple cases
   ;;so map1, map2...
   (cases ((= ?lists ()))
	  ((= ?lists (?list)) (map1 ?predicator ?list))
	  ((= ?lists (?list-1 ?list-2)) (map2 ?predicator ?list-1 ?list-2))
	  ((firsts-and-rests ?arguments ?rest-of-lists ?lists)
	   (?predicator . ?arguments)
	   (map ?predicator . ?rest-of-lists))
	  ((all-nil ?lists)))))

(define-predicate map1
  ((map1 ? ()))
  ((map1 ?predicator (?first . ?rest))
   (?predicator ?first)
   (map1 ?predicator ?rest)))

(define-predicate map2
  ((map2 ? () ()))
  ((map2 ?predicator (?first-1 . ?rest-1) (?first-2 . ?rest-2))
   (?predicator ?first-1 ?first-2)
   (map2 ?predicator ?rest-1 ?rest-2)))

(define-predicate all-nil
  ((all-nil ()))
  ((all-nil (() . ?rest))
   (all-nil ?rest)))

(define-predicate firsts-and-rests
  ((firsts-and-rests () () ()))
  ((firsts-and-rests (?first-first . ?firsts)  (?first-rest . ?rests)
		     ((?first-first . ?first-rest) . ?rest))
   (firsts-and-rests ?firsts ?rests ?rest)))


