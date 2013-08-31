;;; -*- Mode:LISP; Package:PUSER; Base:10; Options:((WORLD CPROLOG)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


(define-cp cp-lisp-value
  ((cp-lisp-value ?x ?y)
   (:prolog (ground ?y) (lisp-value ?x ?y))
   (cut)))

(define-cp cp-not-lisp-value
  ((cp-not-lisp-value ?x ?y)
   (:prolog (ground ?y) (cannot-prove (lisp-value ?x ?y)))
   (cut)))

(define-cp :ordinary-top-level
  (:options (:world :concurrent-prolog-top-level))
  ((:ordinary-top-level)
   (:prolog (remove-world :concurrent-prolog-top-level))
   (cut)))

(define-cp outstream
  ((outstream ()))
  ((outstream (?elt . ?elts))
   (:prolog (ground ?elt) (print ?elt))
   (cut)
   (outstream ??elts)))

;;Matrix Multiply

(define-cp mmtest 
 ((mmtest) (mmtest j j))
 ((mmtest ?x ?y)
  (mm-data ?x ?l1)
  (mm-data ?y ?l2)
  (mm ??l1 ??l2 ?w)
  (:at (outstream ?w) :back)))

(define-cp mm 
 ((mm () ? ())) 
 ((mm (?x . ?xs) ?ys (?z . ?zs))
  (:at (vm ?x ??ys ?z) :right)
  (:at (mm ??xs ?ys ?zs) :forward)))

(define-cp vm 
 ((vm ? () ())) 
 ((vm ?xs (?y . ?ys) (?z . ?zs))
  (ip ??xs ??y ?z)
  (:at (vm ?xs ??ys ?zs) :forward)))

(define-cp ip 
 ((ip ?xs ?ys ?z) (ip ?xs ?ys 0 ?z))
 ((ip (?x . ?xs) (?y . ?ys) ?z0 ?z)
  (cp-lisp-value ?z1 (+ (* ?x ?y) ?z0))
  (ip ??xs ??ys ?z1 ?z))
 ((ip () () ?z ?z)))

(define-cp mm-data 
 ((mm-data a ((3 4) (3 4)))) 
 ((mm-data b ((2 3) (2 3)))) 
 ((mm-data j ((3 2 1 0) (4 3 2 1) (0 4 3 2) (0 0 4 3)))) 
 ((mm-data k ((4 3 2 1 0 0) (5 4 3 2 1 0) (6 5 4 3 2 1) (0 6 5 4 3 2) (0 0 6 5 4 3) (0 0 0 6 5 4)))))

;;Insert Sort

(define-cp btest
 ((btest)
  (:at (bsort (5 3 5 6 45 2 34 6 34 246 23 43 56) ?x) :forward)
  (outstream ??x)))

(define-cp bsort 
 ((bsort (?x . ?xs) (?y . ?ys))
  (bfilter ?x ??xs ?xs1 ?y)
  (:at (bsort ??xs1 ?ys) :forward))
 ((bsort () ())))

(define-cp bfilter 
 ((bfilter ?x1 (?x2 . ?xs) (?x2 . ?ys) ?y)
  (cp-lisp-value t (< ?x1 ?x2))
  (cut)
  (bfilter ?x1 ??xs ?ys ?y))
 ((bfilter ?x1 (?x2 . ?xs) (?x1 . ?ys) ?y)
  (cp-lisp-value nil (< ?x1 ?x2))
  (cut)
  (bfilter ?x2 ??xs ?ys ?y))
 ((bfilter ?x () () ?x)))

;;Sieve of Eratosthenes

(define-cp cpprimes 
 ((cpprimes) (:at (cpprimes ?x) :forward) (outstream ??x))
 ((cpprimes ?j) (integers 2 ?i) (:at (sift ??i ?j) :forward)))

(define-cp integers 
 ((integers ?n (?n . ??i)) (cp-lisp-value ?n1 (+ ?n 1)) (integers ?n1 ?i)))

(define-cp sift 
 ((sift (?p . ?i) (?p . ??r1)) (filter ?i ?p ?r) (:at (sift ??r ?r1) :forward)))

(define-cp filter 
 ((filter (?n . ?i) ?p ?r)
  (cp-lisp-value 0 (\ ?n ?p))
  (cut)
  (filter ?i ?p ?r))
 ((filter (?n . ?i) ?p (?n . ??r))
  (cp-not-lisp-value 0 (\ ?n ?p))
  (cut)
  (filter ?i ?p ?r)))
 
;;Aleph Trees

(define-cp aleph 
 ((aleph)
  (aleph 4))
 ((aleph ?x)
  (aleph ?x ?))
 ((aleph 0 ?r)
  (leaf ?r))
 ((aleph ?n1 ?r14)
  (cp-lisp-value t (> ?n1 0))
  (cp-lisp-value ?n (- ?n1 1))
  (cut)
  (aleph1 ?n ?r1)
  (:at (arm ?n ?r1 ?r12) :right (:forward (- (^ 2 ?n) 1)) :left (:forward (^ 2 ?n)) :left)
  (:at (aleph1 ?n ?r3) (:forward (^ 2 ?n)) :right (:forward (^ 2 ?n)) :left)
  (:at (arm ?n ?r3 ?r34) (:forward (- (^ 2 ?n) 1)) :right (:forward (^ 2 ?n)))
  (:at (internal ?r12 ?r34 ?r14) (:forward (^ 2 ?n)) :right (:forward (^ 2 ?n)) :left)))

(define-cp aleph1
  ;;this is to delay one cyle
  ((aleph1 ?n ?r) (aleph ?n ?r)))

(define-cp leaf 
 ((leaf ?)))

(define-cp internal 
 ((internal ? ? ?)))

(define-cp arm 
 ((arm ?n ?r1 ?r12) (aleph ?n ?r2) (internal ?r1 ?r2 ?r12)))

;;Tower of Hanoi

(define-cp hanoi
 ((hanoi) (:at (hanoi 3) :right))
 ((hanoi 0 ?from ?to (?from ?to))) 
 ((hanoi ?n1 ?from ?to (?before ((?from ?to) ?after)))
  (cp-lisp-value t (> ?n1 0))
  (cp-lisp-value ?n (- ?n1 1))
  (cut)
  (free ?from ?to ?free)
  (:at (hanoi ?n ?from ?free ?before) :left (:forward (^ 2 ?n)))
  (:at (hanoi ?n ?free ?to ?after) :right (:forward (^ 2 ?n))))
 ((hanoi ?n ?x) (hanoi ?n a c ?x))
 ((hanoi ?n) (hanoi ?n ?)))

(define-cp free 
 ((free a b c)) 
 ((free a c b)) 
 ((free b a c)) 
 ((free b c a)) 
 ((free c a b)) 
 ((free c b a)))

(comment ;;Not used in any demos.

;;Naive Reverse
(define-cp cpreverse 
 ((cpreverse () ()))
 ((cpreverse (?x . ?xs) ?zs)
  (:at (cpreverse ??xs ?ys) :forward)
  (cpappend ??ys (?x) ?zs)))

(define-cp cpappend 
 ((cpappend () ?x ?x)) 
 ((cpappend (?x . ?xs) ?ys (?x . ?zs)) (cpappend ??xs ?ys ?zs)))

(define-cp cpreverse-list30
 ((cpreverse-list30 ?x)
  (cpreverse (1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0) ?x)))

;;"Dynamic"
(define-cp table 
 ((table (?w) ?w))
 ((table ?ws ?min)
  (:prolog (not-= ?ws (?)))
  (cut)
  (:at (row ?ws ?ws1) :right)
  (:at (table ?w?s1 ?min) :forward)))

(define-cp row 
 ((row (?) ())) 
 ((row (?w1 ?w2 . ?ws) (?w . ??ws1))
  (entry ?w1 ?w2 ?w)
  (:at (row (?w2 . ?ws) ?ws1) :forward)))

(define-cp entry 
 ((entry (?w1 ?l1 ?r1) (?w2 ?l2 ?r2) (?w ?l1 ?r2))
  (cp-lisp-value ?w (min (+ ?w1 (* (* ?l1 ?r1) ?r2)) (+ ?w2 (* (* ?l1 ?l2) ?r2))))))

(define-cp dyn 
 ((dyn)
  (:at (initial_row (10 20 50 1 100) ?ws) :right)
  (:at (table ??ws ?x) :forward)
  (:at (outstream (solution ?x)) :back)))

(define-cp initial_row 
 ((initial_row (?) ())) 
 ((initial_row (?w1 ?w2 . ?ws) (?w . ??ws1))
  (initial_entry ?w1 ?w2 ?w) (:at (initial_row (?w2 . ?ws) ?ws1) :forward)))

(define-cp initial_entry 
 ((initial_entry ?w1 ?w2 (0 ?w1 ?w2))))

;;"Hex"
(define-cp test 
 ((test ?x ?y)
  (matrix ?x ?d ?m1)
  (matrix ?y ?d ?m2)
  (cut)
  (mm ?d ?m1 ?m2 ?z)
  (outstream ?z)))

(define-cp hex 
 ((hex) (test j j)))

(define-cp mm 
 ((mm ?d ?as ?bs ?cs)
  (mm1 ?d ??as ?bs (c ?cl ?c ?cr))
  (:at (cpreverse ??cl (?c . ??cr) ?cs) :back)))

(define-cp mm1 
 ((mm1 ?d (?ain . ?asin) (?bin . ?bsin) (c ?clout ?cout ?crout))
  (spawn_isp ?d 0 ??cin ?cout ??ain ?aout ??bin ?bout)
  (:at (arm ?d ??asin ?asout ?clin ?clout ?bout) :forward)
  (:at (arm ?d ??bsin ?bsout ?crin ?crout ?aout) :right :forward)
  (cp-lisp-value ?d1 (- ?d 1))
  (:at (mm1 ?d1 ??asout ??bsout (c ?clin ?cin ?crin))
       :forward :right :forward :left))
 ((mm1 ?d () () (c () () ()))))

(define-cp forward 
 ((forward 0 ?cin ?cin ?cout ?cout)) 
 ((forward ?n1 ?cin ?cin2 ?cout ?cout2)
  (cp-lisp-value t (> ?n1 0))
  (cut)
  (cp-lisp-value ?n (- ?n1 1))
  (get_c ?c ?cin ?cin1)
  (send ?c ?cout ?cout1)
  (forward ?n ??cin1 ?cin2 ?cout1 ?cout2)))

(define-cp get_c 
 ((get_c 0 () ()))
 ((get_c ?c (?c . ?cs) ?cs)))

(define-cp arm 
 ((arm ?d ?asin ?asout ?cin ?cout ?bin) (arm ?d 1 ?asin ?asout ?cin ?cout ?bin))
 ((arm ?d ?v () () () (()) ?)) 
 ((arm ?d ?v (?ain . ?asin) (?aout . ?asout) (?cin . ?csin) (?cout . ?csout) ?bin)
  (spawn_isp ?d ?v ??cin ?cout ??ain ?aout ??bin ?bout)
  (cp-lisp-value ?v1 (+ ?v 1))
  (:at (arm ?d ?v1 ??asin ?asout ?csin ?csout ?bout) :forward)))

(define-cp spawn_isp 
 ((spawn_isp 0 ?v ?cin ?cout ?ain ?aout ?bin ?bout)
  (isp ?cin ?cout ?ain ?aout ?bin ?bout)) 
 ((spawn_isp ?d ?v ?cin ?cout ?ain ?aout ?bin ?bout)
  (cp-lisp-value t (> ?d 0))
  (cut)
  (cp-lisp-value ?min (min ?d ?v))
  (forward ?min ?ain ?ain1 ?aout ?aout1)
  (isp ?cin ?cout ??ain1 ?aout1 ?bin ?bout))
 ((spawn_isp ?d ?v ?cin ?cout ?ain ?aout ?bin ?bout)
  (cp-lisp-value t (< ?d 0))
  (cut)
  (cp-lisp-value ?d1 (- ?d))
  (forward ?d1 ??cin ?cin1 ?cout ?cout1)
  (isp ??cin1 ?cout1 ?ain ?aout ?bin ?bout)))

(define-cp isp 
 ((isp ?cin (?c1 . ?cout) (?a . ?ain) (?a . ?aout) (?b . ?bin) (?b . ?bout))
  (get_c ?c ?cin ?cin1)
  (cp-lisp-value ?c1 (+ ?c (* ?a ?b)))
  (cut)
  (isp ??cin1 ?cout ??ain ?aout ??bin ?bout))
 ((isp ?cs ?cs ?as ?as () ())) 
 ((isp ?cs ?cs () () ?bs ?bs)))

(define-cp send 
 ((send ?x (?x . ?xs) ?xs)))

(define-cp receive 
 ((receive ?x (?x . ?xs) ??xs)))

(define-cp cpreverse 
 ((cpreverse () ?x ?x)) 
 ((cpreverse (?x . ?xs) ?ys ?zs)
  (cpreverse ??xs (?x . ?ys) ?zs)))

(define-cp matrix 
 ((matrix a 1 ((1 1) (2 2 2) (3 3) (4)))) 
 ((matrix b 2 ((1) (2 2) (3 3 3) (4 4)))) 
 ((matrix b1 2 ((1) (2 2) (3 3 3)))) 
 ((matrix c 0 ((1)))) 
 ((matrix d 1 ((1) (2 2) (3)))) 
 ((matrix e 1 ((1 2)))) 
 ((matrix f 0 ((1 2) (4)))) 
 ((matrix h 1 ((1 1) (2 2 2) (3 3)))) 
 ((matrix i 1 ((1 1) (2 2 2) (3 3) (4)))) 
 ((matrix j 2 ((1 1) (2 2 2) (3 3 3 3) (4 4 4)))) 
 ((matrix j1 2 ((1 1) (2 2 2) (3 3 3 3)))) 
 ((matrix j2 1 ((2 2 2) (3 3 3 3)))) 
 ((matrix j3 3 ((1) (1 1) (2 2 2) (3 3 3 3)))) 
 ((matrix j4 2 ((1) (2 2) (3 3 3)))) 
 ((matrix k 3 ((1 1 1) (2 2 2 2) (3 3 3 3 3) (4 4 4 4 4 4) (5 5 5 5 5) (6 6 6 6)))) 
 ((matrix amm 1 ((4) (3 4) (3)))) 
 ((matrix ja 2 ((1 1) (2 2 2) (3 3 3 3) (4 4 4)))) 
 ((matrix jb 2 ((1 1) (2 2 2) (3 3 3 3) (4 4 4)))))

;;a Prolog Interpreter in Concurrent Prolog written by Ken Kahn

(define-cp pr
  ((pr ?query)
   (prove (and ?query (and (prolog (print ?query)) (fail))))))

(define-cp prove
  ((prove (true)))
  ((prove (and (true) ?b) (prove ?b)))
  ((prove (and ?a ?b))
   (system ?a)
   (cut)
   (sequential-and ?a ?b))
  ((prove (and ?a ?b))
   (clauses ?a ?clauses)
   (cut)
   (try-each ?clauses ?a ?b)))

(define-cp try-each
  ((try-each ((?goal ?ignore-guard ?body) . ?) ?goal ?cont)
   (prove (and ?body ?cont))
   (cut))
  ((try-each (? . ?more-clauses) ?goal ?cont)
   (:at (try-each ?more-clauses ?goal ?cont) :forward)
   (cut)))

(define-cp sequential-and
  ((sequential-and ?a ?b)
   ?a (cut) ?b))

;;sample predicate to test

(define-cp mem
  ((mem ?x (?x . ?)))
  ((mem ?x (? . ?rest)) (mem ?x ?rest)))

)
