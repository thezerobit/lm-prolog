;;; -*- Mode: Lisp; Base: 10.; Package: Prolog; Options: ((World Benchmarks)); -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;these are benchmarks copied from D.H.D. Warren's University of Edinburgh report #40.

(define-predicate help
  ((help)
   (lisp-value ?help prolog:*benchmarks-help*)
   (format t "~%~a" ?help)))

(define-predicate benchmarks
  ((benchmarks)
   (can-prove (naive-reverse-list30 ?)) (can-prove (naive-reverse-list30 ?)) 
   (can-prove (quick-sort-list50 ?))    (can-prove (quick-sort-list50 ?)) 
   (can-prove (deriv-times10 ?))        (can-prove (deriv-times10 ?))
   (can-prove (deriv-divide10 ?))       (can-prove (deriv-divide10 ?))
   (can-prove (deriv-log10 ?))          (can-prove (deriv-log10 ?))
   (can-prove (deriv-ops8 ?))           (can-prove (deriv-ops8 ?))
   (can-prove (palin25 ?))              (can-prove (palin25 ?))
   (can-prove (dbquery1 ?))             (can-prove (dbquery2 ?))
   (can-prove (dbquery3 ?))             (can-prove (dbquery4 ?))))

(define-predicate concatenate (:options (:argument-list (+ + -)))
  ((concatenate (?first . ?rest) ?back (?first . ?all-but-first))
   (concatenate ?rest ?back ?all-but-first))
  ((concatenate () ?back ?back)))

(define-predicate naive-reverse (:options (:argument-list (+ -)))
  ((naive-reverse (?first . ?rest) ?reverse)
   (naive-reverse ?rest ?rest-reversed)
   (concatenate ?rest-reversed (?first) ?reverse))
  ((naive-reverse () ())))

(define-predicate naive-reverse-list30
  ((naive-reverse-list30 ?x)
   (no-clock-interrupts)
   (time-and-print
     (naive-reverse
       (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
          21 22 23 24 25 26 27 28 29 30)
       ?x)
     ";;Naive Reverse of List 30 long")))

(define-predicate partition (:options (:argument-list (+ + - -)))
 ((partition (?X . ?L) ?Y (?X . ?L1) ?L2)
  (> ?Y ?X)
  (cut)
  (partition ?L ?Y ?L1 ?L2))
 ((partition (?X . ?L) ?Y ?L1 (?X . ?L2))
  (partition ?L ?Y ?L1 ?L2))
 ((partition () ? () ())))

(define-predicate partition
  (:options (:argument-list (+ + - -)) (:world :benchmarks-without-cut))
  ((partition (?x . ?l) ?y ?l1 ?l2)
   ;;;Warren used a cut (as above) instead of Cases of course
   (cases ((> ?y ?x)
           (= ?l1 (?x . ?list-1))
           (partition ?l ?y ?list-1 ?l2))
          ((= ?l2 (?x . ?list-2))
           (partition ?l ?y ?l1 ?list-2))))
  ((partition () ? () ())))

(define-predicate quick-sort (:options (:argument-list (+ - +)))
  ;;Warren's variable names... 
  ((quick-sort (?x . ?l) ?r ?r0)
   (partition ?l ?x ?l1 ?l2)
   (quick-sort ?l2 ?r1 ?r0)
   (quick-sort ?l1 ?r (?x . ?r1)))
  ((quick-sort () ?r ?r)))

(define-predicate quick-sort-list50
  ((quick-sort-list50 ?X)
   (no-clock-interrupts)
   (time-and-print
     (quick-sort (27 74 17 33 94 18 46 83 65 2 32 53 28 85 99 47 28 82 6 11
                  55 29 39 81 90 37 10 0 66 51 7 21 85 27 31 63 75 4 95 99
                  11 28 61 74 18 92 40 53 59 8)
                 ?x ())
     ";;Quick Sort of a list 50 long")))

(define-predicate d (:options (:argument-list (+ + -)))
  ((d (+ ?U ?V) ?X (+ ?DU ?DV))
   (cut) (d ?U ?X ?DU) (d ?V ?X ?DV))
  ((d (- ?U ?V) ?X (- ?DU ?DV))
   (cut) (d ?U ?X ?DU) (d ?V ?X ?DV))
  ((d (* ?U ?V) ?X (+ (* ?DU ?V) (* ?U ?DV)))
   (cut) (d ?U ?X ?DU) (d ?V ?X ?DV))
  ((d (// ?U ?V) ?X (// (- (* ?DU ?V) (* ?U ?DV)) (^ ?V 2)))
   (cut) (d ?U ?X ?DU) (d ?V ?X ?DV))
  ((d (^ ?U ?N) ?X (* ?DU (* ?N (^ ?U ?N1))))
   (cut)
   (number ?N)
   (difference ?n1 ?n 1) ;;was lisp-value ...
   (d ?U ?X ?DU))
  ((d (- ?U) ?X (- ?DU)) (cut) (d ?U ?X ?DU))
  ((d (exp ?U) ?X (* (exp ?U) ?DU)) (cut) (d ?U ?X ?DU))
  ((d (log ?U) ?X (// ?DU ?U)) (cut) (d ?U ?X ?DU))
  ((d ?X ?X 1) (cut))
  ((d ? ? 0)))

(define-predicate d
  (:options (:argument-list (+ + -)) (:world :benchmarks-without-cut))
  ((d (+ ?U ?V) ?X (+ ?DU ?DV)) (d ?U ?X ?DU) (d ?V ?X ?DV))
  ((d (- ?U ?V) ?X (- ?DU ?DV)) (d ?U ?X ?DU) (d ?V ?X ?DV))
  ((d (* ?U ?V) ?X (+ (* ?DU ?V) (* ?U ?DV))) (d ?U ?X ?DU) (d ?V ?X ?DV))
  ((d (// ?U ?V) ?X (// (- (* ?DU ?V) (* ?U ?DV)) (^ ?V 2)))
   (d ?U ?X ?DU) (d ?V ?X ?DV))
  ((d (^ ?U ?N) ?X (* ?DU (* ?N (^ ?U ?N1))))
   (number ?N)
   (difference ?n1 ?n 1)
   (d ?U ?X ?DU))
  ((d (- ?U) ?X (- ?DU)) (d ?U ?X ?DU))
  ((d (exp ?U) ?X (* (exp ?U) ?DU)) (d ?U ?X ?DU))
  ((d (log ?U) ?X (// ?DU ?U)) (d ?U ?X ?DU))
  ((d ?atom ?X ?derivative)
   (not-= ?atom (? . ?))
   (cases ((= ?atom ?x) (= ?derivative 1))
          ((= ?derivative 0)))))

(define-predicate deriv-times10
  ((deriv-times10 ?Y)
   (no-clock-interrupts)
   (time-and-print (d (* (* (* (* (* (* (* (* (* x x) x) x) x) x) x) x) x) x) x ?Y)
         ";;Derivative of 10 nested products")))

(define-predicate deriv-divide10
  ((deriv-divide10 ?Y)
   (no-clock-interrupts)
   (time-and-print (d (// (// (// (// (// (// (// (// (// x x) x) x) x) x) x) x) x) x) x ?Y)
         ";;Derivative of 10 nested quotients")))

(define-predicate deriv-log10
  ((deriv-log10 ?Y)
   (no-clock-interrupts)
   (time-and-print (d (log (log (log (log (log (log (log (log (log x))))))))) x ?Y)
         ";;Derivative of 10 nested logarithms")))

(define-predicate deriv-ops8
  ((deriv-ops8 ?Y)
   (no-clock-interrupts)
   (time-and-print (d (* (+ x 1) (* (+ (^ x 2) 2) (+ (^ x 3) 3))) x ?y)
         ";;Derivative of 8 nested operations")))


;;;;Benchmark 5.4. Serialize.

(define-predicate serialize (:options (:argument-list (+ -)))
  ((serialize ?L ?R) (pairlists ?L ?R ?A) (arrange ?A ?T) (numbered ?T 1 ?)))

(define-predicate before
  (:options (:argument-list (+ +)) (:compile-method :open)) ;;Warren's wasn't open.
  ((before (pair ?X1 ?) (pair ?X2 ?)) (< ?X1 ?X2)))

(define-predicate pairlists (:options (:argument-list (+ - -)))
  ((pairlists (?X . ?L) (?Y . ?R) ((pair ?X ?Y) . ?A)) (pairlists ?L ?R ?A))
  ((pairlists () () ())))

(define-predicate split (:options (:argument-list (+ + - -)))
  ((split (?X . ?L) ?X ?L1 ?L2)
   (cut) (split ?L ?X ?L1 ?L2))
  ((split (?X . ?L) ?Y (?X . ?L1) ?L2)
   (before ?X ?Y) (cut) (split ?L ?Y ?L1 ?L2))
  ((split (?X . ?L) ?Y ?L1 (?X . ?L2))
   (before ?Y ?X) (cut) (split ?L ?Y ?L1 ?L2))
  ((split () ? () ())))

(define-predicate split
  (:options (:argument-list (+ + - -)) (:world :benchmarks-without-cut)) 
  ((split (?X . ?L) ?Y ?L1 ?L2)
   (split ?L ?Y ?rest-L1 ?rest-L2)
   (cases ((= ?x ?y)
           (= ?l1 ?rest-l1)
           (= ?l2 ?rest-l2))
          ((before ?x ?y)
           (= ?l1 (?x . ?rest-l1))
           (= ?l2 ?rest-l2))
          ((= ?l1 ?rest-l1)
           (= ?l2 (?x . ?rest-l2)))))
  ((split () ? () ())))

(define-predicate arrange (:options (:argument-list (+ -)))
  ((arrange (?X . ?L) (tree ?T1 ?X ?T2))
   (split ?L ?X ?L1 ?L2)
   (arrange ?L1 ?T1)
   (arrange ?L2 ?T2))
  ((arrange () void)))

(define-predicate numbered (:options (:argument-list (+ + -)))
  ((numbered (tree ?T1 (pair ? ?N1) ?T2) ?N0 ?N)
   (numbered ?T1 ?N0 ?N1)
   (sum ?n2 ?n1 1) ;;was lisp-value
   (numbered ?T2 ?N2 ?N))
  ((numbered void ?N ?N)))

(define-predicate palin25
  ((palin25 ?Y)
   (no-clock-interrupts)
   (time-and-print
     (serialize (#/a #/b #/l #/e #/  #/w #/a #/s #/  #/i #/  #/e #/r #/e #/   
                     #/i #/  #/s #/a #/w #/  #/e #/l #/b #/a) ?Y)
     ";;Palindrom of list 25 long")))

;;;;Benchmark 5.5. Query.

(define-predicate pop (:options (:argument-list (- -))) ;;not really in Warren's...
  ((pop china 825000)) ;;in thousand people
  ((pop india 586300))
  ((pop ussr 252100))
  ((pop usa 211900))
  ((pop indonesia 127600))
  ((pop japan 109700))
  ((pop brazil 104200))
  ((pop bangladesh 75000))
  ((pop pakistan 68200))
  ((pop w_germany 62000))
  ((pop nigeria 61300))
  ((pop mexico 58100))
  ((pop uk 55900))
  ((pop italy 55400))
  ((pop france 52500))
  ((pop philippines 41500))
  ((pop thailand 41000))
  ((pop turkey 38300))
  ((pop egypt 36400))
  ((pop spain 35200))
  ((pop poland 33700))
  ((pop s_korea 33500))
  ((pop iran 32000))
  ((pop ethiopia 27200))
  ((pop argentina 25100)))
 
(define-predicate area (:options (:argument-list (+ -)))
  ((area china 3380)) ;;in thousand square miles
  ((area india 1139))
  ((area ussr 8708))
  ((area usa 3609))
  ((area indonesia 570))
  ((area japan 148))
  ((area brazil 3288))
  ((area bangladesh 55))
  ((area pakistan 311))
  ((area w_germany 96))
  ((area nigeria 373))
  ((area mexico 764))
  ((area uk 86))
  ((area italy 116))
  ((area france 213))
  ((area philippines 90))
  ((area thailand 20))
  ((area turkey 296))
  ((area egypt 386))
  ((area spain 190))
  ((area poland 121))
  ((area s_korea 37))
  ((area iran 628))
  ((area ethiopia 350))
  ((area argentina 1080)))

(define-predicate indexed-area
  (:options (:indexing-patterns (indexed-area +country -area))
	    (:argument-list (+ -)))
  ((indexed-area china 3380))
  ((indexed-area india 1139))
  ((indexed-area ussr 8708))
  ((indexed-area usa 3609))
  ((indexed-area indonesia 570))
  ((indexed-area japan 148))
  ((indexed-area brazil 3288))
  ((indexed-area bangladesh 55))
  ((indexed-area pakistan 311))
  ((indexed-area w_germany 96))
  ((indexed-area nigeria 373))
  ((indexed-area mexico 764))
  ((indexed-area uk 86))
  ((indexed-area italy 116))
  ((indexed-area france 213))
  ((indexed-area philippines 90))
  ((indexed-area thailand 20))
  ((indexed-area turkey 296))
  ((indexed-area egypt 386))
  ((indexed-area spain 190))
  ((indexed-area poland 121))
  ((indexed-area s_korea 37))
  ((indexed-area iran 628))
  ((indexed-area ethiopia 350))
  ((indexed-area argentina 1080)))

(define-predicate density (:options (:argument-list (- -)))
  ((density ?c ?d)
   (pop ?C ?P)
   (area ?C ?A)
   (quotient ?d ?p ?a)))

(define-predicate indexed-density (:options (:argument-list (- -)))
  ((indexed-density ?c ?d)
   (pop ?C ?P)
   (indexed-area ?C ?A)
   (quotient ?d ?p ?a)))

(define-predicate query (:options (:argument-list (-)))
  ((query (?c1 ?d1 ?c2 ?d2))
   (density ?c1 ?d1)
   (density ?c2 ?d2)
;In LM-Prolog User Manual we have
;   (not-= ?c1 ?c2)
;   (product ?d2-more 1.05 ?d2)
;   ( ?d2 ?d1 ?d2-more)
   (> ?d1 ?d2)
   (product ?d3 20 ?d1)
   (product ?d4 21 ?d2)
   (< ?d3 ?d4)))

(define-predicate bag-query
  ((bag-query (?c1 ?d1 ?c2 ?d2))
   (lazy-bag-of ?country-density (?c ?d) (density ?c ?d))
   (member (?c1 ?d1) ?country-density)
   (member (?c2 ?d2) ?country-density)
   (> ?d1 ?d2)
   (product ?d3 20 ?d1)
   (product ?d4 21 ?d2)
   (< ?d3 ?d4)))

(define-predicate indexed-query (:options (:argument-list (-)))
  ((indexed-query (?c1 ?d1 ?c2 ?d2))
   (indexed-density ?c1 ?d1)
   (indexed-density ?c2 ?d2)
   (> ?d1 ?d2)
   (product ?d3 20 ?d1)
   (product ?d4 21 ?d2)
   (< ?d3 ?d4)))

(define-predicate bag-indexed-query
  ((bag-indexed-query (?c1 ?d1 ?c2 ?d2))
   (lazy-bag-of ?country-density (?c ?d) (indexed-density ?c ?d))
   (member (?c1 ?d1) ?country-density)
   (member (?c2 ?d2) ?country-density)
   (> ?d1 ?d2)
   (product ?d3 20 ?d1)
   (product ?d4 21 ?d2)
   (< ?d3 ?d4)))

(define-predicate dbquery1
  ((dbquery1 ?answer)
   (no-clock-interrupts)
   (time-and-print (bag-of ?answer ?l (query ?L)) ";;Database query")))

(define-predicate dbquery2
  ((dbquery2 ?answer)
   (no-clock-interrupts)
   (time-and-print (bag-of ?answer ?l (bag-query ?L))
         ";;Database query using bags")))

(define-predicate dbquery3
  ((dbquery3 ?answer)
   (no-clock-interrupts)
   (time-and-print (bag-of ?answer ?l (indexed-query ?L))
          ";;Indexed database query")))

(define-predicate dbquery4
  ((dbquery4 ?answer)
   (no-clock-interrupts)
   (time-and-print (bag-of ?answer ?l (bag-indexed-query ?L))
                  ";;Indexed database query using bags")))


