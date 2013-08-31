;;; -*- Mode: Lisp; Package: Prolog; Base: 10; Options: ((WORLD SYSTEM)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;this file contains LM-Prolog predicates for customizing the system

(define-predicate make-true 
  (:options (:lisp-macro-name make-true)
	    (:compile-method :intrinsic compile-make-true)
	    (:argument-list (&rest predications))
	    (:documentation "is an operator upon predications.
 Rather than having predicates for changing the CIRCULARITY-MODE,  the
 UNDEFINED-PREDICATE-MODE,  the OPTION, the current UNIVERSE, the
 handling of INTERRUPTS,  or the PROTECTED-WORLDS, the predicate
 MAKE-TRUE is used.    
 The predication (MAKE-TRUE (CIRCULARITY-MODE :HANDLE)) 
 sets the mode to :HANDLE.
 The predication (MAKE-TRUE (LISP-VALUE 3 *X*)) sets the value
 of the Lisp variable *X* to 3."))
  ((make-true (?predicator . ?arguments))
   (cases ((can-prove (definition ? ?predicator))
	   (either (*make-true* (?predicator . ?arguments))
		   (?predicator . ?arguments)))
	  ((assert ((?predicator . ?arguments))))))
  ((make-true ?predication-1 ?predication-2 . ?more)
   (make-true (and ?predication-1 ?predication-2 . ?more))))

(define-predicate circularity-mode
  (:options (:argument-list (mode))
	    (:documentation "unifies MODE with the current Circularity Mode, 
 which is either :ignore, :handle, or :prevent."))
  ((circularity-mode ?mode-name)
   (lisp-value ?mode-name *circularity-mode*)))

(define-predicate *make-true*
  (:options (:if-old-definition :keep))
  (:change-circularity-mode
    (*make-true* (circularity-mode ?mode-name))
    (lisp-command (set-circularity-mode '?mode-name))))

(define-predicate *current-value-finder*
  (:options (:if-old-definition :keep))
  (:circularity-mode-finder
    (*current-value-finder* (circularity-mode ?ignore-value)
			    (circularity-mode ?))))

(define-predicate undefined-predicate-mode
  (:options (:argument-list (mode))
	    (:documentation "unifies MODE with the current Undefined Predicate Mode,
 which is either :signal, or :fail."))
  ((undefined-predicate-mode ?mode-name)
   (lisp-value ?mode-name *undefined-predicate-mode*)))

(define-predicate *make-true*
  (:options (:if-old-definition :keep))
  (:change-undefined-predicate-mode
    (*make-true* (undefined-predicate-mode ?mode-name))
    (lisp-command (set-undefined-predicate-mode '?mode-name))))

(define-predicate *current-value-finder*
  (:options (:if-old-definition :keep))
  (:undefined-predicate-mode-finder
    (*current-value-finder* (undefined-predicate-mode ?ignore-value)
			    (undefined-predicate-mode ?))))

;(define-predicate delayed-value-mode
;  (:options (:argument-list (mode))
;	    (:documentation "inspects the default mode of interfacing Prolog and Lisp.
; Unifies MODE with the default action taken when Prolog calls
; Lisp. The value can be :copy, :invoke, :query, or .
; It is :query initially."))
;  ((delayed-value-mode ?mode)
;   (lisp-value ?mode *default-lisp-form-mode*)))

;(define-predicate *make-true*
;  (:options (:if-old-definition :keep))
;  (:change-delayed-value-mode
;    (*make-true* (delayed-value-mode ?mode))
;    (lisp-command (set-default-lisp-form-mode '?mode))))

;(defun set-default-lisp-form-mode (mode)
;  (cond ((memq mode '(:invoke  :query :copy))
;	 (setq *default-lisp-form-mode* mode))
;	(t (prolog-error ':bad-delayed-value-mode
;			 "~s should be either :invoke  :query :copy"
;			 mode))))

;(define-predicate *current-value-finder*
;  (:options (:if-old-definition :keep))
;  (:delayed-value-mode-finder
;    (*current-value-finder* (delayed-value-mode ?ignore-value)
;			    (delayed-value-mode ?))))

(define-predicate protected-worlds
  ((protected-worlds ?worlds)
   (lisp-value ?worlds *protected-worlds*)))

(define-predicate *make-true*
  (:options (:if-old-definition :keep))
  (:change-protected-worlds
    (*make-true* (protected-worlds ?worlds))
    (lisp-command (setq *protected-worlds* '?worlds) :copy)))

(define-predicate *current-value-finder*
  (:options (:if-old-definition :keep))
  (:protected-worlds-finder
    (*current-value-finder* (protected-worlds ?ignore-worlds)
			    (protected-worlds ?))))

(define-predicate option
  (:options (:argument-list ((option-name &rest values) &optional predicator world universe))
	    (:documentation "unifies VALUES with the default values for DEFINE-PREDICATE
 option OPTION-NAME.  If PREDICATOR is supplied, OPTION-NAME and VALUES are unified with
 option name and values for it."))
  ((option ?option)
   (lisp-value (? . ?options) *default-options*)
   (member ?option ?options))
  ((option ?option ?predicator . ?world-worlds)
   (definition (define-predicate ? (? . ?options) . ?) ?predicator . ?world-worlds)
   (member ?option ?options)))

(define-predicate *make-true*
  (:options (:if-old-definition :keep))
  (:change-default-option
    (*make-true* (option ?option))
    (lisp-command (set-default-define-option '?option) :copy))
  (:change-predicates-options
    ;;the following is not too expensive since the clauses are passed around
    ;;as instances.
    (*make-true* (option (?option-name . ?values) ?predicator . ?world-worlds))
    (definition (define-predicate ? ?old-options . ?clauses)
		?predicator . ?world-worlds)
    (substitute ?new-options
		(?option-name . ?) (?option-name . ?values) ?old-options =)
    (define-predicate ?predicator ?new-options . ?clauses)))

(define-predicate *current-value-finder*
  (:options (:if-old-definition :keep))
  (:option-finder
    (*current-value-finder* (option (?option-name . ?ignore-values) . ?arguments)
			    (option (?option-name . ?) . ?arguments))
    (symbol ?option-name)))

(defun set-default-define-option (option)
  (setq *default-options* (merge-options `(:options ,option) *default-options*)))

;;; This defines predicates in LM-Prolog for Dec-10 Prolog compatibility.

(define-predicate exploden
  (:options (:argument-list (asciis symbol))
	    (:documentation "converts between a symbol and a list of ASCII codes."))
  ((exploden ?asciis ?symbol)
   (cases ((not-variable ?symbol)
	   (lisp-value ?asciis (exploden '?symbol)))
	  ((not-variable ?asciis)
	   (lisp-value ?symbol (implode '?asciis)))
	  ((error :exploden-of-two-variables
		  "can't exploden ~n and ~n" ?asciis ?symbol)))))

(define-predicate compare
  (:options (:argument-list (relation x y))
	    (:documentation "depending on the outcome of comparing X and Y, RELATION is <, =, or >."))
  ((compare ?op ?x ?y)
   (lisp-value ?signum (prolog-compare '?x '?y))
   (rules (?signum ?op) ((-1 <)) ((0 =)) ((+1 >)))))

(define-predicate standard-order
  (:options (:argument-list (x y))
	    (:documentation "succeeds unless Y is before X in the standard order"))
  ((standard-order ?x ?y)
   (lisp-value ?signum (prolog-compare '?x '?y))
   (< ?signum +1)))

(deffun prolog-compare (x y)
  (cond ((or (and (symbolp x) (symbolp y)) (and (stringp x) (stringp y)))
	 (signum (string-compare x y)))
	((and (consp x) (consp y))
	 (let ((signum (prolog-compare (car x) (car y))))
	   (selectq signum
	     (0 (prolog-compare (cdr x) (cdr y)))
	     (otherwise signum))))
	((and (numberp x) (numberp y))
	 (signum (- x y)))
	((and (value-cell-p x) (not (value-cell-p y)))
	 -1)
	((and (value-cell-p y) (not (value-cell-p x)))
	 +1)
	(t (let ((signum (signum (string-compare (type-of x) (type-of y)))))
	     (selectq signum
	       (0 (signum (%pointer-difference x y)))
	       (otherwise signum))))))

(define-predicate quantified-bag-of
  (:options
    (:argument-list (bag globals term &rest +predications))
    (:documentation
      "finds an instantiation of GLOBALS such that BAG is
 a non-empty list of instantiations of TERM in proofs of +PREDICATIONS."))
  ((quantified-bag-of ?bag ?outer ?term . ?predicates)
   (bag-of ?all (?outer . ?term) . ?predicates)
   (subset-of ?all ?outer ?bag)
   (= ?bag (? . ?))))

(define-predicate quantified-set-of
  (:options
    (:argument-list (set globals term &rest +predications))
    (:documentation
      "finds an instantiation of GLOBALS such that SET is
 a non-empty sorted list of instantiations of TERM in proofs of +PREDICATIONS."))
  ((quantified-set-of ?set ?outer ?term . ?predicates)
   (bag-of ?all (?outer . ?term) . ?predicates)
   (subset-of ?all ?outer ?bag)
   (= ?bag (? . ?))
   (sort ?set ?bag standard-order)))

(define-predicate subset-of
  ((subset-of () ? ()))
  ((subset-of ((?key . ?val) . ?rest) ?key (?val . ?answer))
   (subset-of ?rest ?key ?answer))
  ((subset-of ((?key1 . ?) . ?rest) ?key ?answer)
   (subset-of ?rest ?key ?answer)
   (not-= ?key1 ?key)))
