;;; -*- Mode:LISP; Package:Puser; Base:10; Options:((World Sieve)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;a Sieve of Eratosthenes in Prolog using Bags

(define-predicate help
  ((help)
   (lisp-value ?help prolog:*sieve-help*)
   (format t "~%~a" ?help)))

(define-predicate print-primes
  ((print-primes) (primes ?primes) (map print ?primes)))

(define-predicate primes
  ((primes ?primes)
   (lazy-bag-of ?primes ?prime (prime ?prime))))

(define-predicate prime
  ((prime ?prime)
   (lazy-bag-of ?ints ?int (integer-from ?int 2))
   (prime ?prime ?ints))
  ((prime ?prime (?prime . ?)))
  ((prime ?prime (?seed . ?rest))
   (lazy-bag-of ?sifted ?not-multiple (not-multiple ?not-multiple ?seed ?rest))
   (prime ?prime ?sifted)))

(define-predicate integer-from
  ((integer-from ?i ?i))
  ((integer-from ?i+ ?i)
   (sum ?i+1 ?i 1)
   (integer-from ?i+ ?i+1)))

(define-predicate not-multiple
  ((not-multiple ?number ?seed (?number . ?))
   (quotient ?q ?number ?seed)	;fixnum arithmetics
   (cannot-prove (product ?number ?q ?seed)))
  ((not-multiple ?number ?seed (? . ?numbers))
   (not-multiple ?number ?seed ?numbers)))

