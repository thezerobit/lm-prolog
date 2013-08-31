;;; -*- Mode:LISP; Package:PUSER; Base:10 -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;; Peter Henderson's examples of "delayed evaluation".
;;; "Functional Programming" pp. 214--241.

;;; The general programming style is:
;;; Whenever a structure is "generated", delay the computation of some part of it,
;;; typically its rest.

;;; In all these examples, one could use a sort of :ARGUMENT-LIST declaration
;;; instead of PROLOG:CONSTRAIN.

(define-predicate sum-ints
  ((sum-ints ?n ?sum)
   (prolog:constrain ?ints (integers-beginning ?n ?ints))
   (sum-all ?ints 0 ?sum)))

(define-predicate sum-all
  ((sum-all () ?s ?s))
  ((sum-all (?i . ?j) ?s ?u)
   (sum ?t ?s ?i)
   (sum-all ?j ?t ?u)))

(define-predicate first-k
  ((first-k 0 ? ()) (cut))
  ((first-k ?k (?x . ?rest) (?x . ?rest-k))
   (sum ?k-1 ?k -1)
   (first-k ?k-1 ?rest ?rest-k)))

;;; The SAME-FRINGE problem.

(define-predicate same-fringe
  ((same-fringe ?tree1 ?tree2)
   (prolog:constrain ?tree1 (flatten ?tree1 ?flat ()))
   (prolog:constrain ?tree2 (flatten ?tree2 ?flat ()))))

;If there are two FLATTEN producers, then run one of them.
(define-predicate prolog:*combine-constraints*
  (:options (:if-old-definition :keep))
  (flatten
    (prolog:*combine-constraints* :invoke (flatten . ?) (flatten . ?))))

(define-predicate flatten
  ((flatten () ?f ?f)
   (cut))
  ((flatten (?x . ?rest) ?f0 ?f)
   (cut)
   (flatten ?x ?f0 ?f1)
   (prolog:constrain ?f1 (flatten ?rest ?f1 ?f)))
  ((flatten ?x (?x . ?f) ?f)))

;;A Fibonacci series.

(define-predicate fibonaccis
  ((fibonaccis (1 1 . ?series))
   (prolog:constrain ?series (stream-sum ?series (1 . ?series) (1 1 . ?series)))))

(define-predicate stream-sum
  ((stream-sum (?a . ?as) (?b . ?bs) (?c . ?cs))
   (sum ?a ?b ?c)
   (prolog:constrain ?as (stream-sum ?as ?bs ?cs))))

;;A Hamming series.

(define-predicate hamming
  ((hamming ?x)
   (= ?x (1 . ?x235))
   (prolog:constrain ?x235 (merge ?x235 ?x23 ?x5))
   (prolog:constrain ?x23 (merge ?x23 ?x2 ?x3))
   (prolog:constrain ?x2 (mul ?x2 ?x 2))
   (prolog:constrain ?x3 (mul ?x3 ?x 3))
   (prolog:constrain ?x5 (mul ?x5 ?x 5))))

(define-predicate merge
  ((merge ?merged (?u . ?rest1) (?u . ?rest2))
   (merge ?merged ?rest1 (?u . ?rest2)))
  ((merge (?x . ?merged) (?x . ?rest1) (?y . ?rest2))
   (< ?x ?y)
   (prolog:constrain ?merged (merge ?merged ?rest1 (?y . ?rest2))))
  ((merge (?y . ?merged) (?x . ?rest1) (?y . ?rest2))
   (> ?x ?y)
   (prolog:constrain ?merged (merge ?merged (?x . ?rest1) ?rest2))))

(define-predicate mul
  ((mul () () ?))
  ((mul (?x*y . ?rest*y) (?x . ?rest) ?y)
   (product ?x*y ?x ?y)
   (prolog:constrain ?rest*y (mul ?rest*y ?rest ?y))))

;;A Sieve of Eratosthenes using integer streams.

(define-predicate integers-beginning
  ((integers-beginning ?n (?n . ?rest))
   (sum ?n+1 ?n 1)
   (prolog:constrain ?rest (integers-beginning ?n+1 ?rest))))

(define-predicate primes
  ((primes ?primes)
   (integers-beginning 2 ?integers)
   (sift ?primes ?integers)))

(define-predicate sift
  ((sift (?first . ?rest-sifted) (?first . ?rest-integers))
   (no-multiples ?rest-left ?first ?rest-integers)
   (prolog:constrain ?rest-sifted (sift ?rest-sifted ?rest-left))))

;;Write this with one clause to avoid repeated unifications with third arg
;;which is a constrained variable.
;;Having two clauses slows down this particular program tremendously.
(define-predicate no-multiples 
  ((no-multiples ?filtered ?n (?int0 . ?int))
   (cases ((lisp-predicate (zerop (\ '?int0 '?n)) :dont-invoke)
	   (no-multiples ?filtered ?n ?int))
	  ((= ?filtered (?int0 . ?rest-filtered))
	   (prolog:constrain ?rest-filtered (no-multiples ?rest-filtered ?n ?int))))))

(define-predicate print-primes
  ((print-primes) (primes ?primes) (map print ?primes)))

