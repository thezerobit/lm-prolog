;;; -*- Mode: Lisp; Package: User; Base: 10. -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


#-CommonLisp
(progn 'compile

(package-declare pglobal global 256)

(package-declare prolog pglobal 1028 ()
		 (myrefname global prolog))

(package-declare puser pglobal 1028 ()
		 (myrefname global puser))
)

#+COMMONLISP
(PROGN 'COMPILE

(defpackage PGLOBAL
  (:size 256)
  (:use global))

(defpackage PROLOG
  (:size 1028)
  (:use pglobal global))

(defpackage PUSER
  (:size 1028)
  (:use pglobal global)))


(mapc 'globalize				;Using strings here loses if a symbol is already
      'PROLOG:(					;in the GLOBAL package.
	       REPEAT
	       METER
	       ASSERT
	       ASSERTA
	       ASSERTZ
	       DEFINE-PREDICATE
	       ASSUME
	       RETRACT
	       RETRACT-ALL
	       LISP-VALUE
	       LISP-COMMAND
	       LISP-PREDICATE
	       MAKE-TRUE
	       CIRCULARITY-MODE
	       UNDEFINED-PREDICATE-MODE
	       SAME
	       ;call
	       CAN-PROVE
	       CANNOT-PROVE
	       PROVE-ONCE
	       NOT-= ;;is not in the manual but is used in too many files...
	       FAIL
	       ;false
	       ;true
	       ;comment
	       CASES
	       RULES
	       EITHER
	       CUT
	       VARIABLES
	       GROUND
	       VARIABLE
	       NOT-VARIABLE
	       IDENTICAL
	       NOT-IDENTICAL
	       ATOMIC
	       NUMBER
	       FINITE
	       INFINITE
	       ;symbol
	       LISP-TYPE
	       SUM
	       PRODUCT
	       ;difference
	       ;quotient
	       ;map
	       ;read
	       ;prin1
	       ;prin1-then-space
	       ;princ
	       ;print
	       ;pprint
	       ;write
	       ;tyi
	       ;tyo
	       ;format
	       OPEN-FILE
	       Y-OR-N
	       ;load
	       ;compile
	       COMPILE-FILE
	       ;break
	       ;append
	       ;reverse
	       ;length
	       ;nth 
	       SUBSTITUTE
	       ;member
	       ;remove
	       ;delete
	       ;intersection
	       ;union
	       ;sort
	       ;exploden
	       COMPARE
	       STANDARD-ORDER
	       ALL-WORLDS
	       UNIVERSE
	       ADD-WORLD
	       REMOVE-WORLD
	       DESTROY-WORLD
	       SAVE-WORLD
	       ;let
	       WITH
	       WITHOUT-WORLD
	       WITH-WORLD
	       PREDICATOR
	       DEFINED-IN-WORLD
	       PRINT-DEFINITION
	       DEFINITION
	       REMOVE-DEFINITION
	       CLAUSE
	       CLAUSES
	       BAG-OF
	       SET-OF
	       LAZY-BAG-OF
	       LAZY-SET-OF
	       QUANTIFIED-BAG-OF
	       QUANTIFIED-SET-OF
	       GENERATE-NAME
	       GENERATE-SYMBOL
	       TIME-AND-PRINT
	       ;time
	       ;error
	       ;untrace
	       UNTRACE-QUERY
	       ;step
	       WHO-STATE
	       DEFFUN
	       DEFFSUBST
	       DEMOS
	       OPTION
	       ;;the following are used in demos
	       ASK-ABOUT
	       GRAPHICS-DEMOS-STREAM
	       GRAPHICS
	       HELP
	       )
      (circular-list ':PGLOBAL))

