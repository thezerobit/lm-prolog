;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; Options:((WORLD SYSTEM)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;this helps one load and run LM-Prolog demos

;;the following was borrowed from lmdemo;hakdef.lisp

(DEFVAR *DEMO-ALIST*
        NIL
  "Menu item list.  Elements are (name :VALUE <value> :DOCUMENTATION <string>).
   <value>s are either forms to evaluate or lists of shape (MENU name . elements),
   where elements are recursively the same thing.")

(DEFMACRO DEFDEMO (NAME DOCUMENTATION &REST ARGS)
  "For a simple demo, (DEFDEMO <name> <documentation> <form>).
   For a sub-menu, (DEFDEMO <name> <documentation> <sub-menu title> . <elements>)
   where each <element> is a list that looks like the cdr of a defdemo form."
  `(SETQ *DEMO-ALIST*
         (hacks:ADD-OR-UPDATE-DEMO *DEMO-ALIST* ',NAME ',DOCUMENTATION ',ARGS)))

(DEFUN DEMO (&OPTIONAL (ALIST *DEMO-ALIST*) (NAME "Demo:"))
  (SETQ ALIST (SORTCAR (COPYLIST ALIST) #'STRING-LESSP))
  (let ((CHOICE (TV:MENU-CHOOSE ALIST NAME)))
    (IF (EQ (CAR CHOICE) 'hacks:MENU)
        (DEMO (CDDR CHOICE) (CADR CHOICE))
        (catch-error-restart ((error sys:abort) "Exit from demo."
                              (EVAL CHOICE))))))

(define-predicate graphics
  ((graphics :on) (add-world :graphics))
  ((graphics :off) (remove-world :graphics)))

(define-predicate demos
  :(options (documentation "will put up a menu of several self-documenting demos."))
  ((demos) (lisp-command (demo *demo-alist* "Prolog Demos"))))

(defvar *compile-if-needed* ':yes)

(defun load-system (name)
  (cond ((not (eval `(status feature ,name)))
         (selectq *compile-if-needed*
           (:yes
            (make-system name
                         ':compile ':noconfirm ':no-reload-system-declaration))
           (:query
            (make-system name
                         ':compile ':no-reload-system-declaration))
           (otherwise
            (make-system name
                         ':noconfirm ':no-reload-system-declaration)))
         (eval `(sstatus feature ,name)))))

(defvar *demo-systems* ())

(defmacro defdemo-system (name &body arguments)
  `(progn 'compile
          (push-if-not-memq ',name *demo-systems*)
          (defsystem ,name
            (:pathname-default "lmp:library;")
	    #-symbolics (:default-binary-file-type #.user:default-binary-file-type)
            ,@arguments)))

;;(defdemo "Eager Sets and Bags"
;;       "Defines a variant of Sets and Bags that run in their own process"
;;  (load-system 'eager-collections))

(defdemo-system eager-collections
  (:module eager-collections "lmp:experimental;eager")
  (:compile-load eager-collections))

(defdemo "Parallel Prolog"
   "Defines PARALLEL-AND and PARALLEL-OR and a parallel CALL"
   (eager-example 'parallel-prolog))


;(defdemo "A Clock"
;   "Defines the predicate CLOCK which runs three processes to show the time"
;   (eager-example 'clock))


(defun eager-example (example)
  (send standard-output ':clear-screen)
  (selectq example
    (parallel-prolog
     (format t "~%This defines the predicates
 (PROLOG:PARALLEL-AND . ?PREDICATIONS) and (PROLOG:PARALLEL-OR . ?PREDICATIONS)
 which in separate parallel processes explores each clause and
 each predication in the body of a clause.")
     (load-system 'eager-collections)
     (load-system 'parallel-prolog)
     (query-once '(add-world :parallel))
     (query-once '(add-world :parallel-prolog)))
;    (clock 
;     (format t "~%This defines the predicate (CLOCK ?size) which starts up
; parallel processes for each hand of the clock.")
;     (load-system 'eager-collections)
;     (load-system 'clock)
;     (backtracking-turtle))
    ))

(defdemo-system parallel-prolog
  (:module eager-collections "lmp:experimental;eager")
  (:module parallel-prolog "lmp:experimental;parallel")
  (:compile-load eager-collections)
  (:compile-load parallel-prolog (:fasload eager-collections)))

;;(defdemo-system clock
;;  (:module clock "lmp:experimental;clock")
;;  (:compile-load clock))

(defconst *sieve-help*
	  " This defines the predicates:
 (PRIMES ?p), which unifies ?p with the list of all prime numbers, and
 (PRINT-PRIMES), which prints out all prime numbers.

 The list is computed in a demand-driven fashion.")



(defdemo "Sieve of Eratosthenes"
   "Defines the predicate PRIMES in terms of Lazy or Eager bags"
   (progn
     (send standard-output ':clear-screen)
     (princ *sieve-help*)
     (load-system 'prime-sieve)
     (query-once '(add-world :sieve))))

(defdemo-system prime-sieve
  (:module prime-sieve "lmp:experimental;bag-sieve") ;;Prime number generator
; (:module eager-collections "lmp:experimental;eager")
  (:compile-load prime-sieve)
; (:compile-load eager-collections)
  )

(defconst *peano-help*
 (string-append
 " The following predicates are defined in the world :PEANO:
 (PLUS ?sum ?x-1 ?x-2 ... ?x-n)
 (TIMES ?product ?x-1 ?x-2 ... ?x-n)
 (FACTORIAL ?factorial ?n)
 (FIBONACCI ?fibonacci ?n)
 They work upon constructions of numbers using the constructor (functor) 1+.
 E.g.
 ;;What natural numbers ?a and ?b sum to 3?
 1: (PLUS (1+ (1+ (1+ 0))) ?a ?b)

 ;;What natural numbers ?x and ?y satisfy the equation X+2 = (1+Y)*Y ?
 2: (TIMES (1+ (1+ ?x)) (1+ ?y) ?y)

 ;;What natural numbers ?f and ?n satisfy the equation F = N! ?
 3: (FACTORIAL ?f ?n)

 In addition, the recursive predicates 
 (ORDINARY-FACTORIAL ?factorial ?n)
 (ORDINARY-FIBONACCI ?fibonacci ?n)
 are defined in terms to the ordinary Lisp Machine integers.
 ?n must always be provided and be bound to an integer.
 E.g.
 4: (ORDINARY-FACTORIAL ?f 50)"
 #-symbolics
 "
 These examples have been added to the kill ring.
 Type control-<number> control-y to avoid retyping them."
 #+symbolics ""
 "
 The predication (HELP) will repeat this message."))

#+symbolics 
(defsubst zwei:kill-string (ignore) nil)

(defdemo "Peano Arithmetic"
         "Defines the predicates PLUS, TIMES, FACTORIAL, and FIBONACCI as successor arithmetic"
  (progn
    (send standard-output ':clear-screen)
    (princ *peano-help*)
    (load-system 'peano-arithmetic)
    (query-once '(add-world :peano))
    ;;add the following to the kill ring
    (zwei:kill-string "(ORDINARY-FACTORIAL ?f 50)")
    (zwei:kill-string "(FACTORIAL ?f ?n)")
    (zwei:kill-string "(TIMES (1+ (1+ ?x)) (1+ ?y) ?y)")
    (zwei:kill-string "(PLUS (1+ (1+ (1+ 0))) ?a ?b)")
    (format t "~%The world :PEANO added to the universe.~%")))

(defdemo-system peano-arithmetic
  (:module math "math") 
  (:compile-load math))

;;(defdemo "Freeze and Constraints"
;;       "Defines FREEZE and CONSTRAIN control primitives for postponing proofs"
;;  (load-system 'freeze))

(defdemo-system freeze
  (:module constraints "lmp:experimental;freeze")
  (:compile-load constraints))

(defconst *arithmetic-help*
 (string-append
 "This defines the predicates +, *, -, ////, GREATER, and LESS
 in the world :SMART-ARITHMETIC. If these predicates are called with
 too many variables they `freeze' the predication by constraining
 the variables involved.

 E.g.
 1: (AND (GREATER ?x 2) (+ ?sum 2 ?x) (* 9 ?x ?x)) 
    ;;will figure out what ?sum and ?x must be.
 2: (AND (LESS ?x 3) (LESS ?x 5)) ;;will simplify to (less ?x 3)
 3: (AND (LESS ?x 3) (GREATER ?x 5)) ;;will fail"
 #+symbolics ""
 #-symbolics "
 These examples have been added to the kill ring.
 Type control-<number> control-y to avoid retyping them."))

(defdemo "Smart Arithmetic using Constraints"
         "Defines +, *, greater, etc. that allow variables as any argument"
  (progn
    (send standard-output ':clear-screen)
    (format t "~%~a" *arithmetic-help*)
    (load-system 'freeze)
    (load-system 'freeze-examples)
    (query-once '(add-world :smart-arithmetic))
    (zwei:kill-string "(AND (LESS ?x 3) (GREATER ?x 5))")
    (zwei:kill-string "(AND (LESS ?x 3) (LESS ?x 5))")
    (zwei:kill-string "(AND (GREATER ?x 2) (+ ?sum 2 ?x) (* 9 ?x ?x))")
    (format t "~%The world :SMART-ARITHMETIC added to the universe.")))

(defdemo-system freeze-examples
;; (:module frozen-primes "lmp:experimental;frozen-sieve")
  ;;prime number generator using freeze
  (:module smart-math "lmp:experimental;arithmetic")
;;(:compile-load frozen-primes)
  (:compile-load smart-math))

(defdemo "Backtracking Turtle"
         "Defines the usual turtle commands (FORWARD, RIGHT, etc.) that undo upon backtracking"
  (backtracking-turtle t))

(defconst *turtle-help*
 " The predicate (TURTLE-STREAM ?COMMANDS) implements a mapping between
 a list of graphics commands and the screen.
 The commands are executed as they are instantiated.

 Useful commands include the following:

		 (:FORWARD ?DISTANCE) (:BACK ?DISTANCE)
 Moves the turtle forward or backward by ?DISTANCE,
 upon backtracking the turtle will return.

		     (:RIGHT ?ANGLE) (:LEFT ?ANGLE)
 The turtle turns to the right or left the number of degrees in ?ANGLE.
 Undoes it upon backtracking.

			  (:HERE ?X ?Y ?ANGLE)
 Reads the current position and angle of the turtle.

		        (:SETTURTLE ?X ?Y ?ANGLE)
 Moves the turtle to the given position and angle.

		        (:PLACETURTLE ?X ?Y ?ANGLE)
 Moves the turtle to the given position and angle,
 without drawing a line.

 The predicate (POLY ?LIST ?LISTEND ?N ?SIZE) instantiates the
 difference list from ?LIST to ?LISTEND with commands to draw a polygon
 with ?N sides of size ?size.  The predicate (DRAW-POLYGONS) is
 a simple example; try it.

 The predicate (CIRCLE ?LIST ?LISTEND ?SIZE) generates commands
 to draw a circle.

 Use these e.g. as (AND (TURTLE-STREAM ?S0) (POLY ?S0 ?S1 7 40.) (CIRCLE ?S1 () 80.))")

(defun backtracking-turtle (&optional describe-turtle-predicates-p)
  (cond (describe-turtle-predicates-p
	 (send standard-output ':clear-screen)
	 (princ *turtle-help*)))
  (load-system 'freeze)
  (load-system 'backtracking-turtle)
  (query-once '(add-world :turtle))
  (query-once '(add-world :graphics))
  (format t "~%The worlds :GRAPHICS and :TURTLE have been added to universe.")
  (print-help-for-split-window)
  (puser:prolog-with-turtle))

(defun print-help-for-split-window ()
  (format t "
Type any character when you are ready to go to a split window
in which the bottom is a Prolog Listener,
and the top is for the graphics.
Type System-Greek-P to return to a full window.
")
  (send standard-input ':tyi))

(defvar puser:*turtle-type-in-window*)

(defun force-kbd-input (window query)
;  (send window ':force-kbd-input #.*roman-ii*)
  #+symbolics (dotimes (i (array-active-length query))
		(send window ':force-kbd-input (aref query i)))
  #-symbolics (send window ':force-kbd-input query))

(defun split-screen (help-text query)
  (load-system 'split-screen)
  (print-help-for-split-window)
  (puser:prolog-without-turtle)
  (send puser:*turtle-type-in-window* ':clear-screen)
  (send puser:*turtle-type-in-window* ':string-out help-text)
  (force-kbd-input puser:*turtle-type-in-window* query))

(defdemo-system split-screen
  (:module split-screen "split")
  (:compile-load split-screen))

(defdemo-system backtracking-turtle
  (:module split-screen "split")
  (:module turtle-graphics "turtle")
  (:compile-load split-screen)
  (:compile-load turtle-graphics (:fasload split-screen) (:fasload split-screen)))

(defdemo "Ask About"
         "Lets you define predicates to ask the user the first time a problem is encountered"
  (load-ask-about t))

(defun load-ask-about (&optional describe-self-p)
 (cond (describe-self-p
        (send standard-output ':clear-screen)
        (format t "
 The predicate ASK-ABOUT is being defined.  It is called as
 (ASK-ABOUT ?predicator)
 (ASK-ABOUT ?predicator ?world)
 It defines ?predicator so that the first time it is asked something it queries
 the user and remembers the answer.
 For example, consider the following GRANDPARENT program:

 (define-predicate grandparent
   ((grandparent ?grandparent ?grandchild)
    (parent ?grandparent ?parent) (parent ?parent ?grandchild)))
  
 (define-predicate parent
   ((parent ?parent ?child)
    (or (father ?parent ?child) (mother ?parent ?child))))

 (ask-about father)
 (ask-about mother)

 Try it with your family.")
        #-symbolics
        (format t "~%(You can avoid re-typing the program above by typing control-y)")
        (zwei:kill-string
"(and (define-predicate grandparent
        ((grandparent ?grandparent ?grandchild)
         (parent ?grandparent ?parent) (parent ?parent ?grandchild)))
      (define-predicate parent
        ((parent ?parent ?child)
         (or (father ?parent ?child) (mother ?parent ?child))))

      (ask-about father)
      (ask-about mother))")))
 (load-system 'ask-about))

(defdemo-system ask-about
  (:module ask-about "askabout")
  (:compile-load ask-about))

(defconst *grammar-kit-help*
        " The grammar kit is defined in the world :GRAMMAR.
 It contains the predicate PARSE which can be used as follows:
 (PARSE ?sentence)
 (PARSE ?sentence ?tree)

 If the world :GRAPHICS is before :GRAMMAR then the tree
 will be drawn for you.
 The predication (GRAPHICS :ON) insures this is true.
 (GRAPHICS :OFF) turns it off.

 In addition, the predicate DEFINE-RULES is available for 
 writing grammar rules.
 (DEFINE-RULES ?name-of-part-of-speech . ?rules)
 where each rule is
 (--> (?name-of-part-of-speech . ?arguments) . ?constituents)
 If the ?name-of-part-of-speech is CALL then the it treated as an escape to Prolog.
 If the ?name-of-part-of-speech is TERMINAL then the argument is a terminal.

 Additional rules may be entered separately.
 E.g.
 (DEFINE-RULES VERB-PHRASE
   (--> (VERB-PHRASE (VERB-PHRASE ?VERB))
        (VERB ?VERB))
   (--> (VERB-PHRASE (VERB-PHRASE ?VERB ?NOUN-PHRASE))
        (VERB ?VERB)
        (NOUN-PHRASE ?NOUN-PHRASE)))
 The sample grammar loaded can be found as lmp:library;sample-grammar lisp.
 ")

(defdemo "Grammar Kit"
         "Defines a backtracking tree drawer and a sample grammar"
  (progn (send standard-output ':clear-screen)
         (princ *grammar-kit-help*)
         (load-ask-about)
         (load-system 'grammar-kit)
	 (query-once '(add-world :sample-grammar))
	 (query-once '(add-world :grammar))
	 (query-once '(add-world :graphics))
         (format t
                 "~%The worlds :GRAMMAR, :GRAPHICS, and :SAMPLE-GRAMMAR added to universe.")
         (backtracking-turtle)))

(defdemo-system grammar-kit
  (:module grammar-kit "grammar")
  (:module sample-grammar "sample-grammar")
  (:compile-load grammar-kit)
  (:readfile sample-grammar (:fasload grammar-kit)))

(defconst *8-queens-help*
        "The 8 Queens Problem is defined in the world :GRAPHICS-DEMOS.
 The problem is to place 8 queens on chess board so that no queen threatens another.
 The implementation is based on constraints.
 It contains the predicate 8-QUEENS which can be used as follows:
 (8-QUEENS)
 (8-QUEENS ?board)

 If the world :GRAPHICS is before :GRAPHICS-DEMOS then the board
 will be drawn for you.
 The predication (GRAPHICS :ON) insures this is true. (GRAPHICS :OFF) turns it off.
")

(defconst *knights-tour-help*
	"The Knights Tour Problem is defined in the world :GRAPHICS-DEMOS.
 The problem is to let a knight visit all positions on a chess board exactly once.
 The strategy used here is to select the move that gives the fewest possible
 next moves.
 The problem is solved with a non-deterministic algorithm by the predication
 (KNIGHTS-TOUR) or
 (KNIGHTS-TOUR ?solution)

 If the world :GRAPHICS is before :GRAPHICS-DEMOS then the board will be drawn for you.
 The predication (GRAPHICS :ON) insures this is true. (GRAPHICS :OFF) turns it off.

")

(defconst *send-more-money-help*
	"The Send More Money Problem is defined in the world :GRAPHICS-DEMOS.
 It solves the cryptarithmetics problem SEND + MORE = MONEY.
 The implementation of the solution is based on constraints.
 The problem is solved by the predication
 (SEND-MORE-MONEY) or
 (SEND-MORE-MONEY ?send ?more ?money).

 If the world :GRAPHICS is before :GRAPHICS-DEMOS then the solution will be drawn for you.
 The predication (GRAPHICS :ON) insures this is true. (GRAPHICS :OFF) turns it off.
")

(defdemo-system graphics-demos
  (:module graphics "graphics")
  (:module graphics-demos "graphics-demos")
  (:compile-load graphics)
  (:compile-load graphics-demos))

(defdemo "8 Queens Problem"
	 "Solves the problem of placing 8 queens safely on a chess board"
  (progn (load-system 'freeze)
	 (load-system 'graphics-demos)
	 (query-once '(add-world :graphics-demos))
	 (query-once '(add-world :graphics))
	 (format t "~%The worlds :GRAPHICS-DEMOS and :GRAPHICS added to the universe.")
	 (split-screen *8-queens-help* "(8-queens)")))

(defdemo "Knights Tour"
	 "Solves the problem of having a knight visit all chess board positions once."
  (progn (load-system 'freeze)
	 (load-system 'graphics-demos)
	 (query-once '(add-world :graphics-demos))
	 (query-once '(add-world :graphics))
	 (format t "~%The worlds :GRAPHICS-DEMOS and :GRAPHICS added to the universe.")
	 (split-screen *knights-tour-help* "(knights-tour)")))

(defdemo "Cryptarithmetics"
	 "Solves the SEND + MORE = MONEY problem, where each letter stands for some digit."
  (progn (load-system 'freeze)
	 (load-system 'graphics-demos)
	 (query-once '(add-world :graphics-demos))
	 (query-once '(add-world :graphics))
	 (format t "~%The worlds :GRAPHICS-DEMOS and :GRAPHICS added to the universe.")
	 (split-screen *send-more-money-help* "(send-more-money)")))



(defdemo "Benchmarks"
         "Defines and runs Warren's Prolog Benchmarks"
  (select-benchmarks 'benchmarks))

(defconst *benchmarks-help* "
 Files are being loaded which add predicates to the worlds
 :BENCHMARKS and :BENCHMARKS-WITHOUT-CUT, containing
 several Prolog benchmarks published by David Warren in the
 DAI Research Report No. 40 at the University of Edinburgh,
 May 1977.
 He tested the DECsystem-10 Prolog implementation on a KI-10 processor.
 His findings in cpu seconds were
 
                     Interpreted             Compiled
 Naive Reverse             1.156                 .054
 Quick Sort                1.344                 .075
 Symbolic Derivative
  - 10 nested products      .077                 .003
  - 10 nested quotients     .084                 .003
  - 10 nested logarithms    .049                 .002
  -  8 nested operations    .064                 .002
 Serialize (Palindrom)      .602                 .040
 Data Base Query           8.888                 .185
 ")

(deffun select-benchmarks (predicate)
  (send standard-output ':clear-screen)
  (princ *benchmarks-help*)
  (format t "~%The benchmarks you selected are ~a"
          (selectq predicate
            (interpreted-benchmarks
             "Warren's original programs interpreted.")
            (benchmarks
             "Warren's original programs compiled.")
            (benchmarks-without-cut
             "the programs compiled,
 but re-written to avoid using CUT.")
            (interpreted-benchmarks-without-cut
	     "the programs interpreted,
 but re-written to avoid using CUT.")))
  (load-system 'benchmarks)
  (query-once '(add-world :benchmarks))
  (format t "~%Everything loaded, the world :BENCHMARKS added to the universe.~%")
  (query-once (list predicate)))

(defdemo-system benchmarks
  (:module benchmarks "benchmarks")
  (:compile-load benchmarks))

(defdemo "Different Prolog Top Levels"
         "Presents a Menu of different Top Levels for Prolog written in Prolog"
  "Ordinary Top Levels"
  ("Ordinary Top Level"
   "Print bindings for each proof"
   (select-prolog-top-level ':ordinary-top-level))
  ("Unique Answers only"
   "Print bindings of each element of Lazy Set of solutions to predication"
   (select-prolog-top-level ':unique-answers-top-level))
  ("Compute Ahead for more solutions"
   "Print bindings of each element of Eager Bag of solutions to predication"
   (select-prolog-top-level ':compute-ahead-top-level))
;  ("Lazy set of all solutions"
;   "Given a query (?term . ?predication) prints ?TERM in each proof of ?PREDICATION"
;   (select-prolog-top-level ':lazy-set-top-level))
  ("Parallel Prolog"
   "Computes all conjunctions and disjunctions in parallel"
   (select-prolog-top-level ':parallel-prolog-top-level))
  ("Concurrent Prolog"
   "Ehud Shapiro's Concurrent Prolog with Bagel Simulator"
   (select-prolog-top-level ':concurrent-prolog-top-level)))

(defconst *compute-ahead-help*
        " Files are being loaded for parallel processing.
 This top level starts a separate process to compute the answers
 to the top-level predication.  As soon as one is found it will be
 displayed and the process continues to look for more solutions.
 The predication (:ORDINARY-TOP-LEVEL) restores things to normal.")

(defconst *parallel-prolog-help*
        " Files are being loaded which define a parallel Prolog.
 All disjunctions and conjunctions are explored in parallel.
 The conjunctions, however, can be rather inefficient.
 The predication (:ORDINARY-TOP-LEVEL) restores things to normal.")

(defconst *concurrent-prolog-top-level-help*
 " This runs Concurrent Prolog programs.
 The programs are defined using
 (DEFINE-CP <name>
   (<head-1> [<guard-1> (CUT)] <body-1>)   
   ...
   (<head-n> [<guard-n> (CUT)] <body-n>))

 Read only variables begin and end in a ?, e.g. ?x?.
 (:PROLOG <goal>) escapes to LM-Prolog.
 The predication (:ORDINARY-TOP-LEVEL) restores things to normal.")

(defconst *unique-answers-help*
        " This differs from the ordinary top level in that the
 same set of bindings will not be repeated even if there are
 redunant ways of computing them.
 The predication (:ORDINARY-TOP-LEVEL) restores things to normal.")

(defconst *lazy-set-top-level-help*
        " To this top level queries are given as (?TERM . ?PREDICATION).
 The system will print out a list of instantiations of ?TERM for
 each proof of ?PREDICATION.  Duplicates are removed.
 This works even if there are an infinite number of elements in the answer.
 In such a case one type control-abort to stop more answers from being printed.
 The predication (:ORDINARY-TOP-LEVEL) restores things to normal.")

(defconst *ordinary-top-level-help*
        " This is the ordinary top level that prints variable bindings for
 successive proofs.")

(defconst *bagel-help*
 " This is Ehud Shapiro's Concurrent Prolog system extended to simulate a bagel.
 A Bagel is a grid of processors in the shape of a torus.  The processors on the
 top edge are connected to one on the bottom and one unit to the right.
 Processors on the right edge are connected to the the left edge one down, etc.
 The extension to Concurrent Prolog is that one can optionally specify which
 processor a process should be run upon.  The notation for mapping processes to
 processors is turtle commands such as (:forward 2), :right, etc.
 The simulator shows the state of each processor by showing either an abbreviation
 or the name of the current goal being reduced.
 The predication (GRAPHICS :OFF) switches off the Bagel display. Initially it is on.
 (GRAPHICS :ON) switches it on again.
 Including the world :CP-BF gives breadth-first scheduling;  including :CP-DF
 gives depth-first.  Breadth-first is the default.
 (CPTOP ?goal) runs a goal in Concurrent Prolog.
 ")

(deffun select-prolog-top-level (world)
  (setq *universe* (cons world (remove world *universe*)))
  (send standard-output ':clear-screen)
  (selectq world
    (:compute-ahead-top-level
     (princ *compute-ahead-help*)
     (load-system 'parallel-prolog))
    (:parallel-prolog-top-level
     (eager-example 'parallel-prolog)
     (terpri)
     (princ *parallel-prolog-help*))
    (:unique-answers-top-level
     (princ *unique-answers-help*))
;    (:lazy-set-top-level
;     (princ *lazy-set-top-level-help*))
    (:ordinary-top-level
     (princ *ordinary-top-level-help*))
    (:concurrent-prolog-top-level
     (princ *concurrent-prolog-top-level-help*)
     (terpri)
     (load-system 'cp)))
  (set-universe (cons world (remove world *universe*))))

;;(defdemo-system pure-printer
;;  (:module backtracking-printer "pure-print")
;;  (:compile-load backtracking-printer))


(defdemo "Bagel Simulator"
	 "Shapiro's Concurrent Prolog and the Bagel Parallel Processor Simulator"
  "Bagel Simulator"
  ("Sieve of Eratosthenes"
   "Primes numbers generated in an infinite pipe"
   (cp-demo ':primes))
  ("Bubble Sort"
   "Bubble Sort implemented as a pipe"
   (cp-demo ':bsort))
  ("Matrix Multiply"
   "Naive Matrix Multiply running in a rectangular grid"
   (cp-demo ':mm))
;  ("Matrix Multiply (II)"
;   "Matrix Multiply running in a rectangular grid using streams"
;   (cp-mm-2))
  ("Tower of Hanoi"
   "Tower of Hanoi solved in an H-tree"
   (cp-demo ':hanoi))
  ("Aleph Trees"
   "Densely packed tree structure"
   (cp-demo ':aleph)))

(defconst *cp-primes-help*
 " This defines the Sieve of Eratosthenes in Concurrent Prolog where each filter
 is arranged in a line (pipe).
")

(defconst *cp-bsort-help*
 " This defines bubble sort in Concurrent Prolog where each filter 
 is arranged in a line (pipe).
")

(defconst *cp-mm-help*
 " This defines a matrix multiply in Concurrent Prolog where parallel lines
  of processes computing vector multiplications are created.
")

(defconst *cp-hanoi-help*
 " The Tower of Hanoi in Concurrent Prolog where the computation tree is mirrored
 in the Bagel.
")

(defconst *cp-aleph-help*
 " A densely packed tree is created which could be running a computation whose
 structure is tree-like (e.g. doubly recursive programs).
")

(defun cp-demo (name)
  (send standard-output ':clear-screen)
  (princ *bagel-help*)
  (load-system 'freeze)
  (load-system 'cp)
  (query-once '(add-world :cprolog))  
  (query-once '(add-world :graphics))
  (format t "~%The worlds :CPROLOG and :GRAPHICS added to universe.")
  (selectq name
    (:primes (split-screen *cp-primes-help* "(cptop(cpprimes))"))
    (:bsort (split-screen *cp-bsort-help* "(cptop(btest))"))
    (:mm (split-screen *cp-mm-help* "(cptop(mmtest)))"))
    (:hanoi (split-screen *cp-hanoi-help* "(cptop(hanoi))"))
    (:aleph (split-screen *cp-aleph-help* "(cptop(aleph))"))))

(defdemo-system cp
  (:module graphics "graphics")
  (:module cprolog "cprolog")
  (:module cp-examples "cp-examples")
  (:compile-load graphics)
  (:compile-load cprolog (:fasload graphics) (:fasload graphics))
  (:readfile cp-examples))
