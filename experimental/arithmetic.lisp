;;; -*- Mode: Lisp; Package: Puser; Base: 10.; Options: ((World smart-arithmetic)) ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.

(define-predicate help
  ((help)
   (lisp-value ?help prolog:*arithmetic-help*)
   (format t "~%~a" ?help)))

(define-predicate +
  ((+ . ?args)
   (prolog:freeze (solve (+ . ?args)) 1)))

(define-predicate *
  ((* . ?args)
   (prolog:freeze (solve (* . ?args)) 1)))

(define-predicate -
  ((- . ?args)
   (prolog:freeze (solve (- . ?args)) 1)))

(define-predicate //
  ((// . ?args)
   (prolog:freeze (solve (// . ?args)) 1)))

(define-predicate greater
  ((greater . ?args)
   (prolog:freeze (solve (greater . ?args)) 0)))

(define-predicate less
  ((less . ?args)
   (prolog:freeze (solve (less . ?args)) 0)))

(define-predicate solve
  ((solve (+ ?sum . ?addends))
   (vars-and-nonvars ?vars ?nonvars ?addends)
   (cases ((= () ?vars)
	   (lisp-value ?sum (apply '+ '?nonvars)))	;X = 111+222+...
	  ((not-variable ?sum)
	   (= ?vars (?var . ?))
	   (length ?length ?vars)		;111 = X+222+X+333 ==>
	   (lisp-value ?var
		       (// (- '?sum (float (apply '+ '?nonvars)))	;X = (555-111)/2
			   ?length)))
	  ((variable ?sum)
	   (lisp-value 0 (apply '+ '?nonvars))
	   (rules (?sum)
		  (?vars)			;X = X+0
		  ((0))))))
  ((solve (* ?product . ?factors))
   (vars-and-nonvars ?vars ?nonvars ?factors)
   (cases ((= () ?vars)
	   (lisp-value ?product (apply '* '?nonvars)))	;X = 111*222*...
	  ((not-variable ?product)
	   (= ?vars (?var . ?))
	   (length ?length ?vars)		;a = X*b*X*c
	   (lisp-value ?nvproduct (apply '* '?nonvars))
	   (cases (( 0 ?nvproduct)
		   (lisp-value ?var-unsigned
			       (^ (// '?product (float '?nvproduct))	;X = sqrt((b*c)/a)
				  (// (float '?length))))
		   (signed-= ?var ?var-unsigned ?length))
		  ((= ?product 0))))
	  ((variable ?product)
	   (cases ((lisp-value 1 (apply '* '?nonvars))
		   (rules (?product) (?vars) ((1))))
		  ((= ?product 0))))))
  ((solve (- ?difference ?number ?subtrahend))
   (solve (+ ?number ?subtrahend ?difference)))
  ((solve (// ?quotient ?dividend ?divisor))
   (solve (* ?dividend ?divisor ?quotient)))
  ((solve (greater . ?args)) (lisp-predicate (apply '> '?args)))
  ((solve (less . ?args)) (lisp-predicate (apply '< '?args))))

(define-predicate signed-=
  ((signed-= ?x ?x ?))
  ((signed-= ?x ?us ?n)
   (lisp-predicate (evenp '?n))
   (lisp-value ?x (- '?us))))

(define-predicate vars-and-nonvars
  ((vars-and-nonvars ?vars ?nonvars ?list)
   (vars-and-nonvars ?vars ?nonvars ?list () ()))
  ((vars-and-nonvars ?vars ?nonvars () ?vars ?nonvars))
  ((vars-and-nonvars ?vars ?nonvars (?x . ?y) ?vars0 ?nonvars0)
   (variable ?x)
   (vars-and-nonvars ?vars ?nonvars ?y (?x . ?vars0) ?nonvars0))
  ((vars-and-nonvars ?vars ?nonvars (?x . ?y) ?vars0 ?nonvars0)
   (not-variable ?x)
   (vars-and-nonvars ?vars ?nonvars ?y ?vars0 (?x . ?nonvars0))))

(define-predicate prolog:*combine-constraints*
  :(options (world system) (if-old-definition keep))
  (:simplification-of-two-greaters		;the clause label
    (prolog:*combine-constraints* ((greater ?x ?bigger))
                                  (prolog:freeze (solve (greater ?x ?smaller)) 0)
				  (prolog:freeze (solve (greater ?x ?bigger)) 0))
    ( ?bigger ?smaller))
  (:simplification-of-two-lesses
    (prolog:*combine-constraints* ((less ?x ?smaller))
                                  (prolog:freeze (solve (less ?x ?smaller)) 0)
				  (prolog:freeze (solve (less ?x ?bigger)) 0))
    ( ?bigger ?smaller))
  (:incompatible-less-and-greater
    (prolog:*combine-constraints* :fail
                                  (prolog:freeze (solve (less ?x ?smaller)) 0)
				  (prolog:freeze (solve (greater ?x ?bigger)) 0))
    ( ?bigger ?smaller)))
