;;;  -*- Mode: Lisp; Package: Puser; Base: 10.; Options: ((World Peano)); -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;factorial and fibonacci in LM-Prolog, first without using built-in predicates

(define-predicate help
  ((help)
   (lisp-value ?help prolog:*peano-help*)
   (format t "~%~a" ?help)))

(define-predicate plus
  ((plus 0))
  ((plus ?sum 0 . ?addends)
   (plus ?sum . ?addends))
  ((plus (1+ ?sum) (1+ ?x) . ?addends)
   (plus ?sum ?x . ?addends)))

(define-predicate times
  ((times (1+ 0)))
  ((times 0 0 . ?))
  ((times ?product (1+ ?x-1) . ?multiplicands)
   (times ?product-m . ?multiplicands)
   (times ?product-y ?x-1 ?product-m)
   (plus ?product ?product-y ?product-m)))

(define-predicate factorial
  ((factorial (1+ 0) 0))
  ((factorial ?factorial (1+ ?n-1))
   (factorial ?factorial-of-n-1 ?n-1)
   (times ?factorial (1+ ?n-1) ?factorial-of-n-1)))

(define-predicate fibonacci
  ((fibonacci 0 0))
  ((fibonacci (1+ 0) (1+ 0)))
  ((fibonacci ?fib (1+ (1+ ?x)))
   (fibonacci ?a (1+ ?x))
   (fibonacci ?b ?x)
   (plus ?fib ?a ?b)))

;;now for the more efficient versions

(define-predicate ordinary-factorial :(options (argument-list (factorial +n)))
  ((ordinary-factorial 1 0))
  ((ordinary-factorial ?f ?n)
   (> ?n 0) ;;otherwise can loop on negative numbers while backtracking
   (difference ?n-1 ?n 1)
   (ordinary-factorial ?factorial-of-n-1 ?n-1)
   (product ?f ?factorial-of-n-1 ?n)))

(define-predicate ordinary-fibonacci :(options (argument-list (fibonacci +n)))
  ((ordinary-fibonacci 0 0))
  ((ordinary-fibonacci 1 1))
  ((ordinary-fibonacci ?fib ?n)
   (difference ?n-1 ?n 1)
   (ordinary-fibonacci ?a ?n-1)
   (difference ?n-2 ?n-1 1)
   (ordinary-fibonacci ?b ?n-2)
   (sum ?fib ?a ?b)))


