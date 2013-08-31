;;; -*- Mode: Lisp; Package: Puser; Base: 10. ; Options: ((World Grammar)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;; Cleaned up using the Turtle stream by Mats Carlsson.

;;; Compiler.

(define-predicate define-rules
  (:options (:lisp-macro-name define-rules))
  ((define-rules ?name . ?rules)
   (define-predicate ?name (:options (:place-clauses :after) (:type :dynamic)))
   (and . ?rules)))

(globalize 'define-rules 'pglobal)

(define-predicate -->
  (:options (:lisp-macro-name -->))
  ((--> (?part-of-speech . ?arguments) . ?constitutents)
   (translate--> ?new-constitutents ?constitutents ?S0 ?S ?P1 ?P)
   (assert ((?part-of-speech ?S0 ?S ?P0 ?P . ?arguments)
	    (display-terminal 0 ?p0 ?p1 ?part-of-speech)
	    . ?new-constitutents))))

(define-predicate translate-->
  ((translate--> ?new-constituents ?constituents ?s0 ?s ((:here ?x ?y ?) . ?p0) ?p)
   (length--> ?l 0 ?constituents)
   (trans-clause--> ?new-constituents ?constituents ?s0 ?s ?p0 ?p 0 ?l ?x ?y)))

(define-predicate length-->
  ((length--> ?l ?l ()))
  ((length--> ?l ?l0 ((call . ?) . ?rest))
   (length--> ?l ?l0 ?rest))
  ((length--> ?l ?l0 (? . ?rest))
   (sum ?l1 ?l0 1)
   (length--> ?l ?l1 ?rest)))

(define-predicate trans-clause-->
  ((trans-clause--> () () ?s ?s ?p ?p ?n ?n ? ?))
  ((trans-clause--> (?call . ?new-rest) ((call ?call) . ?rest) ?s0 ?s ?p0 ?p ?n0 ?n ?x ?y)
   (trans-clause--> ?new-rest ?rest ?s0 ?s ?p0 ?p ?n0 ?n ?x ?y))
  ((trans-clause--> ((word ?word . ?args) (display-terminal 0 ?p0 ?p1 ?word) . ?new-rest)
		    ((is-word ?word . ?args) . ?rest)
		    (?word . ?s0) ?s ((:placeturtle ?x ?y ?theta) . ?p0) ?p ?n0 ?n ?x ?y)
   (angle--> ?n ?n0 ?n1 ?theta)
   (trans-clause--> ?new-rest ?rest ?s0 ?s ?p1 ?p ?n1 ?n ?x ?y))
  ((trans-clause--> ((display-terminal 0 ?p0 ?p1 ?word) . ?new-rest)
		    ((terminal ?word . ?) . ?rest)
		    (?word . ?s0) ?s ((:placeturtle ?x ?y ?theta) . ?p0) ?p ?n0 ?n ?x ?y)
   (angle--> ?n ?n0 ?n1 ?theta)
   (trans-clause--> ?new-rest ?rest ?s0 ?s ?p1 ?p ?n1 ?n ?x ?y))
  ((trans-clause-->
     ((?rule ?s0 ?s1 ?p0 ?p1 . ?args) . ?new-rest)
     ((?rule . ?args) . ?rest)
     ?s0 ?s ((:placeturtle ?x ?y ?theta) . ?p0) ?p ?n0 ?n ?x ?y)
   (angle--> ?n ?n0 ?n1 ?theta)
   (trans-clause--> ?new-rest ?rest ?s1 ?s ?p1 ?p ?n1 ?n ?x ?y)))

(define-predicate angle-->
  ((angle--> ?n ?n0 ?n1 ?theta)
   (sum ?n1 ?n0 1)
   (lisp-value ?theta (compute-theta '?n0 '?n))))

(defun compute-theta (n out-of)			;;Mats 860101
  (cond ((> out-of 1) (- (* 120. (- 2 (// (float n) (float (1- out-of))))) 90.0))
	(t 90.0)))


;;; Runtime.

(define-predicate parse 
  ((parse ?sentence)
   (parse ?sentence ?))
  ((parse ?sentence ?tree)
   (parse ?sentence ?tree ?))
  ((parse ?sentence ?tree ?graph)
   (turtle-stream ((:startgrammar) . ?graph))	;;Mats 860101
   (sentence ?sentence () ?graph () ?tree)))

(define-predicate display-terminal
;  ((display-terminal ? ((:markv ?name) . ?p) ?p ?name))
  ((display-terminal ? ?p ?p ?name))
  )

(define-predicate display-terminal
  (:options (:world :graphics) (:deterministic :always))
  ((display-terminal ?fwd ((:forward ?fwd) (:here ?x ?y ?) . ?p0) ?p ?name)
   (cannot-prove (near-some-text ?name ?x ?y))
   (= ?p0 ((:markv ?name) . ?p))
   (assume ((text-displayed-at (?x ?y) ?name)) :graphics))
  ((display-terminal ?fwd0 ?p0 ?p ?name)
   (sum ?fwd ?fwd0 40)
   (display-terminal ?fwd ?p0 ?p ?name)))

(define-predicate size-of-text			;in TURTLE units
  ((size-of-text (?height ?width) ?text)
   (lisp-value ?height (* *tvstep (tv:font-raster-height (send tvrtle-window ':current-font))))
   (lisp-value ?string (string '?text))
   (lisp-value ?width (* *tvstep (send tvrtle-window ':string-length '?string)))))

(define-predicate text-displayed-at
  (:options (:world :graphics) (:type :dynamic)))

(define-predicate near-some-text
  ((near-some-text ?text ?x ?y)
   (size-of-text (?height ?length-of-text) ?text)
   (text-displayed-at (?others-x ?others-y . ?) ?other-text)
   (lisp-value ?y-distance (* 0.7 (abs (- '?y '?others-y))))
   (< ?y-distance ?height)
   (lisp-value ?x-distance (* 1.8 (abs (- '?x '?others-x))))
   (size-of-text (? ?length-of-other-text) ?other-text)
   (sum ?2width ?length-of-text ?length-of-other-text)
   (< ?x-distance ?2width)))

(ask-about word)

(define-predicate help
  ((help)
   (lisp-command (format t "~%~a" prolog:*grammar-kit-help*))))
