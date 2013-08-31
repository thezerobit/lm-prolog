;;; -*- Mode: Lisp; Package: Prolog; Base: 10.; Options: ((World Tests)); -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;this file is for running LM-Prolog through its paces.

;;first, all the predicates in the manual.

(define-predicate define-test (:options (:lisp-macro-name define-test))
  ((define-test ?test-pattern . ?test)
   (lisp-value ?name (intern (format nil "~s" '?test-pattern)))
   ;(define-precate test :(options (if-old-definition keep))
   (assert
      (?name (test ?test-pattern)
	     (format t "~%Trying test ~s" ?test-pattern)
	     (cases ((can-prove (and . ?test))
		     (format t " and it succeeded.") (fail))
		    ((format t " and it FAILED.")))))))

(define-predicate test
  (:options (:type :dynamic)
            (:indexing-patterns (test (+type -number)))
            (:place-clauses :after)))

(define-predicate interpreted-test
  ((interpreted-test ?x) (with-world :interpreted-tests (test ?x))))

(define-test (append 1)
  (append (a b c d e f) (a b) () (c) (d e f) ()))

(define-test (append 2)
  (lazy-bag-of ?answers (?a ?b ?c) (append (a b c) ?a ?b ?c))
  (lazy-bag-of ?checks ok (member ?parts ?answers) (append (a b c) . ?parts))
  (nth ok 5 ?checks))

(define-test (reverse 1)
  (reverse (a b c) (c b a))
  (reverse ?abc (c b a))
  (= ?abc (a b c))
  (reverse ?abc ?cba)
  (= ?cba (c b a)))
  
(define-test (reverse 2)
  (reverse (a b c x y z) (c b a) (x y z)))

(define-test (length 1)
  (length 3 (a b c))
  (length ?n (a b c))
  (= ?n 3)
  (length 3 ?l)
  (= ?l (x y z)))

(define-test (length 2)
  (length 3 (a b c d e f) ?rest)
  (= ?rest (d e f)))

(define-test (nth 1)
  (nth c 2 (a b c d e f))
  (cannot-prove (nth ? 3 (a b)))
  (bag-of ?positions ?n (nth c ?n (a b c q c r)))
  (= ?positions (2 4))
  (nth c 2 ?l)
  (= ?l (? ? c . ?)))

(define-test (remove 1)
  (remove (2 3 4) 1 (1 2 3 1 4 1))
  (remove ?left 3 (4 3 3 3 4))
  (= ?left (4 4)))

(define-test (remove 2)
  (remove ?l (a ?) ((a one) (b two) (a three)))
  (= ?l ((b two))))

(define-test (intersection 1)
  (intersection ?i (a r b c q) (e b f a c) (a b c) (t u c e b a))
  (length 3 ?i)
  (member a ?i) (member b ?i) (member c ?i))
  
(define-test (union 1)
  (union ?u (a r b c q) (e b f a c) (a b c) (t u c e b a))
  (= ?u (u t f e q c b r a)))

(define-test (sort 1)
  (sort ?sorted (2 1 3 4 0) >)
  (= ?sorted (4 3 2 1 0)))

(define-predicate has-fewer-variables
  ((has-fewer-variables ?term-1 ?term-2)
   (variables ?variables-1 ?term-1)
   (variables ?variables-2 ?term-2)
   (length ?n-1 ?variables-1)
   (length ?n-2 ?variables-2)
   (< ?n-1 ?n-2)))

(defvar foo)

(define-test (sort 2)
  (sort ?sorted ((a ?b ?q) (?a ?b ?c) (foo) (?r ?r)) has-fewer-variables)
  (= ?sorted ((foo) (?r ?r) (a ?b ?q) (?a ?b ?c))))

(define-test (substitute 1)
  (substitute ?substituted ?x ?y ((1 . ?x) (2 . ?z)))
  (identical ?substituted ((1 . ?y) (2 . ?z))))

(define-test (substitute 2)
  (substitute ?substituted 1 2 (?x 1 3 5 7) =)
  (identical ?substituted (2 2 3 5 7)))

;lisp interface is used by tests already?

(define-test (same 1)
  (same (?a ?a ?) (? ?b ?b) (?c ? ?c))
  (identical (?a ?b ?c) (?c ?a ?b)))

(define-test (= 1)
  (= (?a ?b ?b) (?c ?c ?d)))

(define-test (= 2)
  (= (?a ?b ?b) (?c ?c ?d))
  (cannot-prove (= (?a . ?b) (1 . 2))))

(define-test (identical 1)
  (identical (1 ?x) (1 ?x))
  (cannot-prove (identical (1 ?x) (1 ?y))))

(define-test (atomic 1)
  (atomic 0) (cannot-prove (atomic ?)) (cannot-prove (atomic (0))))

(define-test (symbol 1)
  (symbol t)
  (cannot-prove (symbol ?))
  (cannot-prove (symbol 0))
  (cannot-prove (symbol (0))))

(define-test (number 1)
  (number 0)
  (cannot-prove (number ?))
  (cannot-prove (number t))
  (cannot-prove (number (0))))

(define-test (variable 1)
  (variable ?)
  (cannot-prove (variable t))
  (not-variable t)
  (cannot-prove (not-variable ?)))

(define-test (variables 1)
  (variables ?v ((1 ?x) (?y 2)))
  (identical ?v (?x ?y)))

(define-test (ground 1)
  (= ?x (1 . ?y))
  (= ?y (2))
  (ground ?x)
  (cannot-prove (ground (((?))))))

(define-test (generate-name 1)
  (generate-name ?name foo)
  (symbol ?name)
  (lisp-predicate (string-equal-symbol "FOO" '?name t) :dont-invoke))

(define-test (sum 1)
  (sum 0)
  (sum 10. 1 2 3 4)
  (= ?x (3 4))
  (sum 10. 1 2 . ?x))

(define-test (product 1)
  (product 1)
  (product 24. 1 2 3 4)
  (= ?x (3 4))
  (product 24. 1 2 . ?x))

(define-test (difference 1)
  (difference 11 23 12))

(define-test (quotient 1)
  (quotient 64. 128. 2.))

(define-test (< 1) ;;should have some conter-examples too...
  (<)
  (< 1 2 3)
  (>)
  (> 3 2 1)
  ()
  ( 1 1 2 2)
  ()
  ( 2 2 1 1))

;;bag-of, can-prove, cannot-prove, cases
;;are used in other tests...

(define-test (lazy-bag-of 1)
  (lisp-command (setq foo 1))
  (lazy-bag-of ?b ?x (member ?x (a b c)) (lisp-command (setq foo '?x)))
  (lisp-value 1 foo)
  (= ?b (a . ?))
  (lisp-value a foo)
  (cannot-prove (member d ?b))
  (= ?b (a b c))
  (lisp-value c foo))

(define-test (set-of 1)
  (set-of (0 1 2) ?x (member ?x (0 0 1 1 2 2))))

(define-test (quantified-bag-of 1)
  (bag-of ?bags (?x . ?bag)
	  (quantified-bag-of ?bag (?x) ?y (member (?x ?y) ((a 1) (? 2) (b 3)))))
  (= ?bags ((a 1 2) (b 2 3))))

(define-test (lazy-set-of 1)
  (lazy-set-of (0 1 2) ?x (member ?x (0 0 1 1 2 2))))

(define-test (if 1)
  (bag-of (2) ?y (if (= ?x 1) (= ?y 2) (= ?y 3))))

(define-test (either 1)
  (bag-of (1) ?y (either (= ?y 1) (= ?y 2) (= ?y 3))))

(define-test (rules 1)
  (bag-of (1 2) ?y
          (rules foo
                 (bar (= ?y 0))
                 (foo (or (= ?y 1) (= ?y 2)))
                 (?y))))

(define-test (unwind-protect 1)
  (or (and (unwind-protect
             (lisp-command (setq foo 0))
             (lisp-command (setq foo 1)))
           (lisp-value 0 foo)
           (fail))
      (lisp-value 1 foo)))

(define-test (unwind-protect 2)
  (or (prove-once (unwind-protect
                    (lisp-command (setq foo 0))
                    (lisp-command (setq foo 1)))
                  (lisp-value 0 foo))
      (lisp-value 1 foo)))

(define-test (map 1)
  (map sum (8 13 18) (1 2 3) (9 12 15) (-2 -1 0))
  ;(map first (?a foo ?c) ((bar zap) (foo silly) ?d))
  ;(= ?a bar) (= ?d (?c . ?))
  (cannot-prove (map > (6 7 8) (1 2 99))))

(define-predicate cut-1
  ((cut-1 1) (or (cut) (lisp-command (setq foo 'no-good))))
  ((cut-1 2)))

(define-test (cut 1)
  (bag-of (1) ?x (cut-1 ?x))
  (cannot-prove (lisp-value no-good foo)))

(define-predicate cut-2
  ((cut-2 ?x) (or (and (cut) (= ?x 1)) (= ?x 2)))
  ((cut-2 3)))

(define-test (cut 2)
  (bag-of (1) ?x (cut-2 ?x)))

(define-predicate cut-3
  ((cut-3 1) (or (and (cut-3 2) (cut) (fail)) (true)))
  ((cut-3 2)))

(define-test (cut 3)
  (cannot-prove (cut-3 1)))

(define-predicate foo (:options (:world :tests) (:type :dynamic)))

(define-test (assert 1)
  (retract-all foo :tests)
  (assert ((foo bar)) :tests)
  (foo bar)
  (assert ((foo bar-2)) :tests)
  (bag-of (bar-2 bar) ?x (foo ?x)))

(define-test (retract 1)
  (retract-all foo :tests)
  (assert ((foo bar)) :tests)
  (assert ((foo bar-2)) :tests)
  (retract ((foo bar)) :tests)
  (bag-of (bar-2) ?x (foo ?x))
  (cannot-prove (retract ((foo . ?)) :jupiter)))

(define-test (retract-all 1)
  (assert ((foo bar)) :tests)
  (assert ((foo bar-2)) :tests)
  (retract-all foo :tests)
  (cannot-prove (foo ?)))

(define-test (remove-definition 1)
  (define-predicate remove-definition-1
    :(options (world tests)))
  (can-prove (definition ? remove-definition-1 :tests))
  (remove-definition remove-definition-1 :tests)
  (cannot-prove (definition ? remove-definition-1 :tests)))

(define-predicate assume-1
  :(options (:world :tests) (type dynamic)))

(define-test (assume 1)
  (or (and (assume ((assume-1 bar)) :tests)
           (assume-1 bar)
           (assume ((assume-1 bar-2)) :tests)
           (bag-of (bar-2 bar) ?x (assume-1 ?x))
           (fail))
      (cannot-prove (assume-1 ?))))

;;more DB tests go here...


(define-test (circularity-mode 1)
  (with (circularity-mode :ignore)
        (with (circularity-mode :handle)
              (= ?x (f ?x))
              (= ?y (f (f ?y)))
              (= ?x ?y)
              (set-of (?) ?x (or (= ?x (f ?x)) (= ?x (f (f ?x))))))))

(define-test (circularity-mode 2)
  (with (circularity-mode :prevent)
        (cannot-prove (= ?x (f ?x))))
  (with (circularity-mode :ignore)
        (= ?x (f ?x))))

(define-test (circularity-mode 3)
  (let (circularity-mode :prevent))
  (cannot-prove (= ?x (f ?x)))
  (let (circularity-mode :ignore))
  (= ?x (f ?x)))

(define-predicate indexing-1
  (:options (:world :tests)
	    (:indexing-patterns (indexing-1 +x y) (indexing-1 x (a +z))))
  ((indexing-1 one))
  ((indexing-1 a (b c)))
  ((indexing-1 a r)))

(define-test (indexing 1)
  (bag-of (a a) ?x (indexing-1 ?x ?))
  (indexing-1 a ?)
  (indexing-1 ? (? c))
  (clauses (? ?) (indexing-1 a ?))
  (clauses (?) (indexing-1 ? (? c)))
  (clauses () (indexing-1 b)))

(define-predicate indexing-2
  (:options (:world :tests)
	    (:type :dynamic)
	    (:indexing-patterns (indexing-2 +x y) (indexing-2 x (a +z)))))

(define-test (indexing 2)
  (retract-all indexing-2 :tests)
  (assert ((indexing-2 a (q c))) :tests)
  (clauses (?) (indexing-2 a ?))
  (assert ((indexing-2 a (q c))) :tests)
  (clauses (? ?) (indexing-2 a ?))
  (assert (foo (indexing-2 a (q c))) :tests)
  (clauses (? ? ?) (indexing-2 a ?))
  (assert (foo (indexing-2 a (q c))) :tests)
  (clauses (? ? ?) (indexing-2 a ?))
  (bag-of ? ? (retract ((indexing-2 a ?)) :tests)))

(define-test (lisp-type 1)
  (lisp-type symbol x)
  (lisp-type fixnum 1)
  (lisp-type cons (? . ?)))

(define-test (lisp-type 2)
  (lazy-bag-of ?b ?x (member ?x (a b c)) (lisp-command (setq foo '?x)))
  (lisp-type cons ?b)
  (lisp-value a foo))

;(define-test (with 1)
;  (lazy-bag-of ?b ?x (member ?x (a b c)) (lisp-command (setq foo '?x)))
;  (with (delayed-value-mode :invoke)
;        (lisp-value (a b c) '?b)
;        (lisp-value c foo)))

(define-predicate abcd
  :(options (if-another-definition try-after)
	    (multiple (options (world tests-1))
		      (options (world interpreted-tests-1))))
  ((abcd a))
  ((abcd b)))

(define-predicate abcd
  :(options (if-another-definition try-before)
	    (multiple (options (world tests-2))
		      (options (world interpreted-tests-2))))
  ((abcd c))
  ((abcd d)))

(define-test (if-another-definition 1)
  (universe ?universe)
  (unwind-protect
    (and (map add-world (:tests-1 :interpreted-tests-1 :tests-2 :interpreted-tests-2))
	 (lazy-bag-of (a b a b c d c d) ?x (abcd ?x))
	 (map add-world (:tests-1 :interpreted-tests-1))
	 (lazy-bag-of (a b a b c d c d) ?x (abcd ?x)))
    (make-true (universe ?universe))))

(define-test (if-another-definition 2)
  (with-world :tests-1
   (with-world :interpreted-tests-1
    (with-world :tests-2
     (with-world :interpreted-tests-2
      (lazy-bag-of (a b a b c d c d) ?x (abcd ?x))))))
  (with-world :tests-2
   (with-world :interpreted-tests-2
    (with-world :tests-1
     (with-world :interpreted-tests-1
      (lazy-bag-of (a b a b c d c d) ?x (abcd ?x)))))))

(define-test (read 1)
  (format t "~%Type the variable ?FROTZ please:")
  (read :foo)
  (format t "~%Type it again please:")
  (cannot-prove (read :bar)))

(define-predicate lam-test
  ((lam-test ?y)
   (lambda ?lam (?y) (1 ?y))
   (?lam 1 2)
   (?lam 1 3)))

(define-test (lambda 1)
  (cannot-prove (lam-test ?))
  (lambda ?lam (?y) (?x ?y))
  (?lam ?a ?b)
  (?lam ?c ?d)
  (not-identical ?a ?c)
  (identical ?b ?d))

(define-predicate same-fringe
  ((same-fringe ?tree-1 ?tree-2)
   (lazy-bag-of ?fringe ?leaf (has-leaf ?leaf ?tree-1))
   (lazy-bag-of ?fringe ?leaf (has-leaf ?leaf ?tree-2))))

;assuming ground tree
(define-predicate has-leaf
  ((has-leaf ?leaf ?leaf)
   (atomic ?leaf))
  ((has-leaf ?leaf (?first . ?))
   (has-leaf ?leaf ?first))
  ((has-leaf ?leaf (? . ?rest))
   (has-leaf ?leaf ?rest)))

(define-predicate file-characters
  ((file-characters ?stream ?file-name)
   (open-file ?lisp-stream ?file-name)
   (lazy-bag-of ?stream ?character
		(tyi-until-eof ?character ?lisp-stream))))

(define-predicate tyi-until-eof
  ((tyi-until-eof ?char ?stream)
   (tyi ?c ?stream -1)
   ( ?c 0)
   (or (= ?c ?char) (tyi-until-eof ?char ?stream))))

