;;; -*- Mode: Lisp; Package: Puser; Base: 10. ; Options:((WORLD GRAPHICS-DEMOS)); -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;; Predicates that draw chess boards.

(define-predicate help
  ((help)
   (lisp-command
     (format t "~%~a~%~a~%~a" prolog:*8-queens-help* prolog:*knights-tour-help* prolog:*send-more-money-help*))))

(define-predicate display-board
  ((display-board ?heading ((:absolute-size ?width ?height) . ?pos0) ?pos)
   (quotient ?xstep ?width 20.)
   (product ?ystep ?xstep .8)
   (lisp-value ?xbase (// (- '?width (* 8 '?xstep)) 2))
   (lisp-value ?ybase (// (- '?height (* 8 '?ystep)) 2))
   (= ?pos0 ((:define-coords ?xbase ?ybase ?xstep ?ystep)
	     (:line 0 0 8 0) (:line 8 0 8 8) (:line 8 8 0 8) (:line 0 8 0 0)
	     . ?pos1))
   (squares 0 0 ?pos1 ((:centered-text ?heading 0 8 -1) . ?pos))))

(define-predicate squares
  ((squares 7 9 ?pos0 ?pos) (cut) (= ?pos0 ?pos))
  ((squares ?row 9 ?pos0 ?pos) (cut) (sum ?row+1 ?row 1) (squares ?row+1 0 ?pos0 ?pos))
  ((squares ?row 8 ?pos0 ?pos) (cut) (sum ?row+1 ?row 1) (squares ?row+1 1 ?pos0 ?pos))
  ((squares ?row ?column ((:rectangle 1 1 ?row ?column) . ?pos0) ?pos)
   (sum ?column+2 ?column 2)
   (squares ?row ?column+2 ?pos0 ?pos)))


;;; Predicates that draw chess pieces.

(send tv:main-screen ':parse-font-descriptor #-3600 'fonts:s30chs #+3600 'fonts:s35ger)

#-3600
(define-predicate queen
  (:options (:compile-method :open))
  ((queen ((:char :s30chs #/b ?x ?y) . ?pos) ?pos ?x ?y)))

#+3600
(define-predicate queen
  :(options (compile-method open))
  ((queen ((:char :s35ger #/Q ?x ?y) . ?pos) ?pos ?x ?y)))

#-3600
(define-predicate knight
  :(options (compile-method open))
  ((knight ((:char :s30chs #/h ?x ?y) . ?pos) ?pos ?x ?y)))

#+3600
(define-predicate knight
  :(options (compile-method open))
  ((knight ((:char :s35ger #/K ?x ?y) . ?pos) ?pos ?x ?y)))

;;; The Eight Queens Problem.

(define-predicate no-threat
  ((no-threat ?y1 ?y2 ?dx)
   (lisp-predicate ( (abs (- '?y1 '?y2)) '?dx) :invoke)))

(define-predicate safe-queen
  ((safe-queen ? () ?) (cut))
  ((safe-queen ?y1 (?y2 . ?rest) ?dx)
   (prolog:constrain ?y2 (no-threat ?y1 ?y2 ?dx))
   (sum ?dx1 ?dx 1)
   (safe-queen ?y1 ?rest ?dx1)))

(define-predicate display-safe-queens
  ((display-safe-queens 8 () ?pos ?pos)
   (cut))
  ((display-safe-queens ?i (?y . ?rest) ?pos0 ?pos)
   (sum ?i1 ?i 1)
   (display-safe-queens ?i1 ?rest ?pos1 ?pos)
   (safe-queen ?y ?rest 1)
   (prolog:constrain ?y (queen ?pos0 ?pos1 ?i ?y))))

(define-predicate 8-queens-solution
  ((8-queens-solution ?l ?pos0 ?pos)
   (display-safe-queens 0 ?l ?pos0 ?pos)
   (sub-permutation (0 1 2 3 4 5 6 7) ?l)))

;;Sub-permutation is defined at the end of this file.

(define-predicate 8-queens 
  ((8-queens)
   (8-queens ?))
  ((8-queens ?v)
   (8-queens ?v ?))
  ((8-queens ?v ?pos0)
   (graphics-demos-stream ?pos0)
   (display-board "8 Queens Problem" ?pos0 ?pos1)
   (time-and-print (8-queens-solution ?v ?pos1 ()))))

;;; The Knights Tour Problem.

;;SIMPLE-LOGICAL-ARRAYS are just arrays of logical variables.
prolog:
(defun simple-logical-array (&rest dimensions)
  (let* ((array (make-array dimensions ':area *prolog-work-area*))
	 (origin (ap-1-force array 0)))
    (dotimes (i (apply #'* dimensions))
      (let ((place (%make-pointer-offset dtp-locative origin i)))
	(rplaca place place)))
    array))

prolog:
(define-predicate 2d-array-element ;;:(options (deterministic always))
  ((2d-array-element ?value ?array ?x ?y)
   (lisp-value ?value (aref '?array '?x '?y)))
   ;;(nth ?row ?x ?array)
   ;;(nth ?value ?y ?row)
  )

prolog:
(define-predicate 2d-array
  ((2d-array ?array ?x ?y)
   (lisp-value ?array (simple-logical-array '?x '?y))))

(define-predicate first-best-move :(options (argument-list (* * +)))
  ((first-best-move ?best ?best ()))
  ((first-best-move ?best ?sofar (?move . ?moves))
   (= (? . ?sl) ?sofar)
   (= (? . ?ml) ?move)
   (cases ((< ?ml ?sl) (first-best-move ?best ?move ?moves))
	  ((first-best-move ?best ?sofar ?moves)))))

(define-predicate best-move
  ((best-move ?pattern ?old-pos ?count (?x . ?y))
   (bag-of (?move . ?moves) (?pos . ?n)
	   (legal-move ?pattern ?old-pos ?count ?pos)
	   (bag-of ?list x (legal-move ?pattern ?pos x ?))
	   (length ?n ?list))
   (first-best-move (? . ?least) ?move ?moves)
   (member ((?x . ?y) . ?least) (?move . ?moves))
   (prolog:2d-array-element ?count ?pattern ?x ?y)))

(define-predicate display-move
  ((display-move (?x0 . ?y0) (?x1 . ?y1) ?pos0 ?pos3)
   (knight ?pos0 ?pos1 ?x0 ?y0)
   (knight ?pos1 ?pos2 ?x1 ?y1)
   (lisp-value ?pos2
	       (prolog:prolog-cons
		 (prolog:prolog-list ':line (+ .5 '?x0) (+ .5 '?y0) (+ .5 '?x1) (+ .5 '?y1))
		 '?pos3)
	      )))

(define-predicate knight-move
  ((knight-move ? ? ?max ?max ?pos ?pos))
  ((knight-move ?pattern ?last-move ?count ?max ?pos0 ?pos)
   (< ?count ?max)
   (sum ?count+1 ?count 1)
   (best-move ?pattern ?last-move ?count ?new-move)
   (display-move ?last-move ?new-move ?pos0 ?pos1)
   (knight-move ?pattern ?new-move ?count+1 ?max ?pos1 ?pos)))

(define-predicate legal-move
  ((legal-move ?pattern (?last-x . ?last-y) ?count (?new-x . ?new-y))
   (knight-delta ?dx ?dy)
   (sum ?new-x ?last-x ?dx)
   ( 0 ?new-x 7)
   (sum ?new-y ?last-y ?dy)
   ( 0 ?new-y 7)
   (prolog:2d-array-element ?count ?pattern ?new-x ?new-y)))

(define-predicate knight-delta
  ((knight-delta -2 -1))
  ((knight-delta -1 -2))
  ((knight-delta +1 -2))
  ((knight-delta +2 -1))
  ((knight-delta +2 +1))
  ((knight-delta +1 +2))
  ((knight-delta -1 +2))
  ((knight-delta -2 +1)))

(define-predicate knights-tour
  ((knights-tour ?pos0)
   (graphics-demos-stream ?pos0)
   (display-board "Knights Tour Problem" ?pos0 ((:fix-mouse "Pick a square" ?mx ?my) . ?pos1))
   (knight ?pos1 ?pos2 ?mx ?my)
   (prolog:2d-array ?pattern 8 8)
   (prolog:2d-array-element 0 ?pattern ?mx ?my)
   (time-and-print (knight-move ?pattern (?mx . ?my) 1 64. ?pos2 ())))
  ((knights-tour)
   (knights-tour ?)))

;;; The Send More Money Problem.

(define-predicate display-equation
  ((display-equation ?heading ?coords ((:absolute-size ?width ?height) . ?pos0) ?pos)
   (either (= ?width 100.) (true))		;default if graphics is off
   (either (= ?height 100.) (true))		;ditto
   (quotient ?xstep ?width 15.)
   (product ?ystep ?xstep .8)
   (lisp-value ?xbase (// (- '?width (* 5 '?xstep)) 2))
   (lisp-value ?ybase (// (- '?height (* 3 '?ystep)) 2))
   (= ?pos0 ((:define-coords ?xbase ?ybase ?xstep ?ystep)
	     (:line -1 2 5 2)
	     (:centered-text ?heading 0 5 -1)
	     . ?pos1))
   (display-equation-1 ?coords ?pos1 ?pos)))

(define-predicate display-equation-1
  ((display-equation-1 () ?pos ?pos) (cut))
  ((display-equation-1 ((?) . ?specs) ?pos0 ?pos)
   (cut)
   (display-equation-1 ?specs ?pos0 ?pos))
  ((display-equation-1 ((?var (?x . ?y) . ?coords) . ?specs) ?pos0 ?pos)
   (prolog:constrain ?var (= ?pos0 ((:digit :43vxms ?var ?x ?y) . ?pos1)))
   (display-equation-1 ((?var . ?coords) . ?specs) ?pos1 ?pos)))

(define-predicate send-more-money
  ((send-more-money)
   (send-more-money ?))
  ((send-more-money ?graph)
   (time-and-print (send-more-money-solution ?graph))))

(define-predicate send-more-money-solution
  ((send-more-money-solution ?pos0)
   (prolog:constrain ?s (> ?s 0))
   (prolog:constrain ?m (> ?m 0))
   (prolog:constrain ?e (add-two-with-carry ?c1 ?y ?d ?e 0))
   (prolog:constrain ?r (add-two-with-carry ?c2 ?e ?n ?r ?c1))
   (prolog:constrain ?o (add-two-with-carry ?c3 ?n ?e ?o ?c2))
   (prolog:constrain ?m (add-two-with-carry ?m  ?o ?s ?m ?c3))
   (graphics-demos-stream ?pos0)
   (display-equation "SEND + MORE = MONEY"
		     ((?y (4 . 2))
		      (?d (4 . 0))
		      (?e (2 . 0) (4 . 1) (3 . 2))
		      (?n (3 . 0) (2 . 2))
		      (?r (3 . 1))
		      (?o (2 . 1) (1 . 2))
		      (?s (1 . 0))
		      (?m (1 . 1) (0 . 2)))
		     ?pos0 ())
   (sub-permutation (0 1 2 3 4 5 6 7 8 9) (?y ?d ?e ?n ?r ?o ?s ?m))))

(define-predicate add-two-with-carry
  ((add-two-with-carry 0 ?sum ?x ?y ?c)
   (lisp-value ?sum (+ '?x '?y '?c) :invoke))
  ((add-two-with-carry 1 ?sum ?x ?y ?c)
   (lisp-value ?sum (+ '?x '?y '?c -10) :invoke)))

(define-predicate sub-permutation
  ((sub-permutation ? ()))
  ((sub-permutation ?all (?x . ?but-one-perm))
   (extraction ?all ?x ?but-one)
   (sub-permutation ?but-one ?but-one-perm)))

(define-predicate extraction
  ((extraction (?x . ?l) ?x ?l))
  ((extraction (?x . ?all) ?y (?x . ?some))
   (extraction ?all ?y ?some)))
