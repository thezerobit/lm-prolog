;;; -*- Mode: Lisp; Package: Prolog; Base: 10; Options: ((World System)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;this file contains the database and "world" handling primitives of LM-Prolog

(define-predicate with-world
  (:options (:compile-method :open)
	    (:argument-list (+world &rest +predications))
	    (:documentation "satisfies +predications with +world temporarily added
 to the current universe."))
  ((with-world ?world . ?predications)
   (universe ?old-worlds)
   (with (universe (?world . ?old-worlds)) (and . ?predications))))

(define-predicate without-world
  (:options (:compile-method :open)
	    (:argument-list (+world &rest +predications))
	    (:documentation "satisfies +predications with +world temporarily removed
 from the current universe."))
  ((without-world ?world . ?predications)
   (universe ?universe)
   (cases ((can-prove (member ?world ?universe)) ;;test not really necessary-Mats
	   (remove ?without-world ?world ?universe)
	   (with (universe ?without-world) (and . ?predications)))
	  ((and . ?predications)))))

(define-predicate define-predicate
  (:options
     (:argument-list (+predicator &rest +options-and-clauses))
     (:documentation
       "defines +PREDICATOR. +OPTIONS-AND-CLAUSES can be either a list of
 clauses, a list of options begining with :options followed by a list of
 clauses, or NIL.  A clause can be either named or not.  An unnamed clause
 is a list of predications.  A named clause is a list beginning with a symbol
 followed by a list of predications.
 Possible options are:
			      (:TYPE +type)
 The possible values of +TYPE are :static and :dynamic.
			     (:WORLD +world)
 +WORLD should be a symbol and describes where the +PREDICATOR's definition 
 should be put.
		     (:IF-ANOTHER-DEFINITION +action)
 This option allows one to control what happens
 if a predicate is defined in more than one world in the current universe.
 Possible values are :before, :after, and :ignore.
		   (:IF-OLD-DEFINITION +keep-or-flush)
 If there already is a predicate of the same name in the same world then
 if +KEEP-OR-FLUSH is :keep the new clauses are added to the old
 predicate, otherwise if it is :flush then the new definition replaces the old
 one. The default is :flush.
			 (:PLACE-CLAUSES +where)
 This option can be used together with (:IF-OLD-DEFINITION :KEEP) and
 controls exactly where the new clauses go. +WHERE can be :before,
 :after,and :anywhere.
		  (:INDEXING-PATTERNS &rest +patterns)
 This option allows for indexed database search when predications of the
 current definition are to be satisfied.  +PATTERNS are a list
 of search patterns that can be used by the theorem prover.
  In an indexing pattern there should be exactly one component beginning with
 a + to specify what the key is.
			  (:DETERMINISTIC +when)
 Both the interpreter and compiled code perform significant
 optimizations if the value of +WHEN is :always.
		     (:COMPILE-METHOD &rest +method)
 This affects the compilation of calls to
 the predicate being defined. +METHOD can be (:closed) for ordinary compilation,
 (:open) for predicates that should compile open, (:intrinsic function-name)
 for predicates with hand-tailored compilation.
			(:ARGUMENT-LIST +pattern)
 This is used for Control-Shift-A in the editor and in the rubout-handler.
 An argument list is a list of symbols and lists.
 A symbol beginning with + indicates that the corresponding element must be
 bound, a symbol beginning with - indicates that it must be unbound, and
 other symbols allow anything in the corresponding position.
 The key words &rest and &optional are also allowed.
		  (:DOCUMENTATION +documentation-string)
 This is accessed by the Control-Shift-D command in
 both the editor and the rubout handler.
		      (:LISP-MACRO-NAME +macro-name)
 This defines a Lisp macro named +MACRO-NAME which executes
 (PROVE-ONCE (+PREDICATOR . ?arguments))."))
  ((define-predicate ?predicator ?options-or-clause-1 . ?clauses-rest)
   (symbol ?predicator)
   (cases ((= ?options-or-clause-1 (:options . ?))
	   (lisp-command
	     (define-predicate-1 '?predicator '?options-or-clause-1 '?clauses-rest)
	     :dont-invoke))
	  ((lisp-command
	     (define-predicate-1 '?predicator nil
	       (cons '?options-or-clause-1 '?clauses-rest))
	     :dont-invoke))))
  ((define-predicate ?predicator)
   (lisp-command (define-predicate-1 '?predicator nil nil)
		 :dont-invoke)))

(define-predicate clause-predicator
  ((clause-predicator ?predicator ((?predicator . ?) . ?))
   (not-variable ?predicator))
  ((clause-predicator ?predicator (?name (?predicator . ?) . ?))
   (either (atomic ?name) (variable ?name))))


(define-predicate assert
  (:options
     (:argument-list (+clause &optional +world +predicator))
     (:documentation "adds +CLAUSE to the definition of +PREDICATOR in +WORLD.
 It is placed according to what the definition says.
 If the +WORLD isn't given then the (option (:world ?WORLD)) is used.
 If the +PREDICATOR isn't given it will be extracted from the +CLAUSE."))
  ((assert ?clause)
   (prove-once (clause-predicator ?predicator ?clause))
   (define-predicate ?predicator
     (:options (:if-old-definition :keep))
     ?clause))
  ((assert ?clause ?world)
   (prove-once (clause-predicator ?predicator ?clause))
   (define-predicate ?predicator
     (:options (:world ?world)
	       (:if-old-definition :keep))
     ?clause))
  ((assert ?clause ?world ?predicator) ;;this is the fastest version
   (define-predicate ?predicator
     (:options (:world ?world)
	       (:if-old-definition :keep))
     ?clause)))

(define-predicate asserta
  (:options
     (:argument-list (+clause &optional +world +predicator))
     (:documentation "adds +CLAUSE to the definition of +PREDICATOR in +WORLD.
 It is placed in front of other clauses.
 If the +WORLD isn't given then the (option (:world ?WORLD)) is used.
 If the +PREDICATOR isn't given it will be extracted from the +CLAUSE."))
  ((asserta ?clause)
   (prove-once (clause-predicator ?predicator ?clause))
   (define-predicate ?predicator
     (:options (:place-clauses :before)
	       (:if-old-definition :keep))
     ?clause))
  ((asserta ?clause ?world)
   (prove-once (clause-predicator ?predicator ?clause))
   (define-predicate ?predicator
     (:options (:world ?world)
	       (:place-clauses :before)
	       (:if-old-definition :keep))
     ?clause))
  ((asserta ?clause ?world ?predicator) ;;this is the fastest version
   (define-predicate ?predicator
     (:options (:world ?world)
	       (:place-clauses :before)
	       (:if-old-definition :keep))
     ?clause)))

(define-predicate assertz
  (:options
     (:argument-list (+clause &optional +world +predicator))
     (:documentation "adds +CLAUSE to the definition of +PREDICATOR in +WORLD.
 It is placed behind other clauses.
 If the +WORLD isn't given then the (option (:world ?WORLD)) is used.
 If the +PREDICATOR isn't given it will be extracted from the +CLAUSE."))
  ((assertz ?clause)
   (prove-once (clause-predicator ?predicator ?clause))
   (define-predicate ?predicator
     (:options (:place-clauses :after)
	       (:if-old-definition :keep))
     ?clause))
  ((assertz ?clause ?world)
   (prove-once (clause-predicator ?predicator ?clause))
   (define-predicate ?predicator
     (:options (:world ?world)
	       (:place-clauses :after)
	       (:if-old-definition :keep))
     ?clause))
  ((assertz ?clause ?world ?predicator) ;;this is the fastest version
   (define-predicate ?predicator
     (:options (:world ?world)
	       (:place-clauses :after)
	       (:if-old-definition :keep))
     ?clause)))



(define-predicate assume
  (:options
     (:argument-list (+clause &optional +world))
     (:documentation "adds the +CLAUSE to the predicate in the +WORLD.
 The predicate is extracted from the +CLAUSE.
 If +WORLD isn't given then its the default defining world.
 The +CLAUSE is removed upon backtracking or abort."))
  ((assume ((?predicator . ?arguments) . ?body))
   (option (:world ?world))
   (assume ((?predicator . ?arguments) . ?body) ?world))
  ((assume ((?predicator . ?arguments) . ?body) ?world)
   (make-clause ?clause ((?predicator . ?arguments) . ?body) ?world ?predicator)
   (unwind-protect (assert ?clause ?world ?predicator)
		   (remove-clause ?clause ?world ?predicator))))

(define-predicate make-clause
  ((make-clause ?clause-instance ?clause ?world ?predicator)
   (symbol ?world)
   (symbol ?predicator)
   (lisp-value ?clause-instance
	       (let ((*contains-cut* nil))
		 (make-clause '?clause '?predicator '?world)))))

(define-predicate ground-assume
  (:options
     (:argument-list (+clause &optional +world))
     (:documentation "This is an experimental (and faster) version of ASSUME"))
  ((ground-assume ((?predicator . ?arguments) . ?body))
   (option (:world ?world))
   (ground-assume ((?predicator . ?arguments) . ?body) ?world))
  ((ground-assume ((?predicator . ?arguments) . ?body) ?world)
   (symbol ?predicator)
   (symbol ?world)
   (lisp-command (ground-assume-clause '((?predicator . ?arguments) . ?body)
				       '?predicator
				       '?world))))

(defun ground-assume-clause (clause predicator world)
  (let ((definition (definition-in-world predicator world)))
    (cond ((null definition)
	   (prolog-error ':undefined-predicate
			 "Can't assume into ~s in ~s since ~s isn't defined in it."
			 clause world predicator))
	  (t (let ((clause
		     (make-instance-in-area *prolog-work-area*
		       'clause
		       ':templates (cons-in-area
				     (make-constant (rest1 (first clause)))
				     (make-constant (rest1 clause))
				     *prolog-work-area*)
		       ':predicator predicator
		       ':world world
		       ':contains-cut nil))
		   (clauses-location
		     (list-in-area *prolog-work-area* ':location (locf (definition-clauses definition)))))
	       (trail
		 (continuation
		   (funcall 'remove-assumption clause clauses-location)))
	       (push-in-area clause (contents (cadr clauses-location)) *prolog-work-area*))))))

(defun remove-assumption (clause clauses-location)
  (setf (contents (cadr clauses-location)) (delq clause (contents (cadr clauses-location)))))

(define-predicate retract
  (:options
     (:argument-list (clause-pattern &optional world))
     (:documentation "retracts the first clause in WORLD to match CLAUSE-PATTERN.
 If WORLD is not given then elements of the universe are used.
 This can backtrack to remove the next matching clause."))
  ((retract ?clause-pattern)
   (retract ?clause-pattern ?))
  ((retract ?clause-pattern ?world)
    (clause-predicator ?predicator ?clause-pattern)
    (definition (define-predicate ? ?options . ?clauses) ?predicator ?world)
    (cases ((member (:type :static) ?options)
	    (error :retract-static-definition 
		   "~S must be dynamic to retract from"
		   ?predicator))
	   ((member ?clause ?clauses)
	    (= ?clause-pattern ?clause)
	    (remove-clause ?clause ?world ?predicator)))))

(define-predicate remove-clause
  ((remove-clause ?clause ?world ?predicator)
   (symbol ?world)
   (symbol ?predicator)
   (lisp-command (remove-clause '?clause
				(definition-in-world '?predicator '?world)))))

(define-predicate remove-clause-named
  ((remove-clause-named ?name ?world ?predicator)
   (symbol ?world)
   (symbol ?predicator)
   (lisp-command (remove-clause-named '?name
				      (definition-in-world '?predicator '?world)))))

(define-predicate remove-all-clauses
  ((remove-all-clauses ?predicator ?world)
   (symbol ?predicator)
   (symbol ?world)
   (lisp-predicate (remove-all-clauses (definition-in-world '?predicator '?world)))))

(define-predicate retract-all
  (:options
     (:argument-list (+predicator &optional +world))
     (:documentation "removes all clauses from the +PREDICATOR defined in +WORLD.
 The predicate is not destroyed, see REMOVE-DEFINITION for that."))
  ((retract-all ?predicator)
   (option (:world ?world))
   (retract-all ?predicator ?world))
  ((retract-all ?predicator ?world)
   (remove-all-clauses ?predicator ?world)))

(define-predicate all-worlds
  (:options
     (:argument-list (+worlds))
     (:documentation
       "unifies +WORLDS with the list of all worlds that have ever been created.
 Only DESTROY-WORLD removes a world from this list."))
  ((all-worlds ?worlds) (lisp-value ?worlds *all-worlds*)))

(define-predicate universe
  :(options
     (:argument-list (+worlds))
     (:documentation
       "unifies +WORLDS with the list of worlds that are in current the universe.
 It is these worlds that are searched for predicate definitions."))
  ((universe ?worlds) (lisp-value ?worlds *universe*)))

(define-predicate *make-true*
  (:options (:if-old-definition :keep))
  (:change-universe
    (*make-true* (universe ?worlds))
    (lisp-command (set-universe '?worlds) :copy)))

(define-predicate *current-value-finder* 
  (:options (:if-old-definition :keep))
  (:universe-finder
    (*current-value-finder* (universe ?ignore-value) (universe ?))))

(define-predicate add-world
  (:options
     (:lisp-macro-name add-world) ;;so that files can do this
     (:argument-list (+world))
     (:documentation "adds +WORLD to the front of the current universe."))
  ((add-world ?world)
   (universe ?all-worlds)
   (remove ?worlds ?world ?all-worlds)
   (make-true (universe (?world . ?worlds)))))

(define-predicate remove-world
  (:options
     (:argument-list (+world))
     (:documentation "removes +WORLD from the current universe."))
  ((remove-world ?world)
   (universe ?all-worlds)
   (remove ?worlds ?world ?all-worlds)
   (make-true (universe ?worlds))))

(define-predicate save-world
  (:options
     (:argument-list (+world +file-name))
     (:documentation
       "saves the definitions of the predicates in +WORLD in +FILE-NAME."))
  ((save-world ?world ?file-name)
   (bag-of ? ?
     (open-file ?stream ?file-name out)
     (lisp-command
      (format '?stream ";;; -*- Mode:LISP; Base:~D; Package:~A -*-~%"
	      base package))
     (definition ?definition ? ?world)
     (tyo #\return ?stream)
     (tyo #\return ?stream)
     (pprint ?definition ?stream))))

(define-predicate destroy-world
  (:options
     (:argument-list (+world))
     (:documentation
       "removes all definitions in +WORLD and removes any references to it."))
  ((destroy-world ?world)
   (symbol ?world)
   (bag-of ? ?
	   (predicator ?predicator ?world)
	   (remove-definition ?predicator ?world))
   (remove-world ?world)
   (lisp-command (setq *all-worlds* (delq '?world *all-worlds*)))))

(define-predicate predicator
  (:options
     (:argument-list (predicator &optional world worlds))
     (:documentation "holds if PREDICATOR is defined in WORLD.
 If WORLD isn't given then an element of WORLDS which defaults to the universe."))
  ((predicator ?predicator)
   (predicator ?predicator ?))
  ((predicator ?predicator ?world)
   (predicator ?predicator ?world ?))
  ((predicator ?predicator ?world ?worlds)
   (cases ((symbol ?world))
	  ((if (variable ?worlds) (universe ?worlds))
	   (member ?world ?worlds)))
   (cases ((variable ?predicator)
	   (predicators ?predicators-in-world ?world)
	   (member ?predicator ?predicators-in-world))
	  ((lisp-predicate (definition-in-world '?predicator '?world))))))

(define-predicate predicators
  ((predicators ?names ?world)
   (symbol ?world)
   (lisp-value ?names (predicators '?world))))

(define-predicate defined-in-world
  (:options
     (:argument-list (world +predicator))
     (:documentation "finds worlds where PREDICATOR is defined."))
  ((defined-in-world ?world ?predicator)
   (defined-in-worlds ?worlds ?predicator)
   (member ?world ?worlds)))

(define-predicate defined-in-worlds
  ;;finds the worlds where the predicator is defined
  ((defined-in-worlds ?worlds ?predicator)
   (symbol ?predicator)
   (lisp-value ?worlds (mapcar #'first (rest1 (definitions '?predicator))))))

(define-predicate apropos
  (:options
     (:argument-list (predicator +substring &optional world worlds))
     (:documentation
       "unifies PREDICATOR with a predicator in WORLD whose name contains +SUBSTRING.
 If WORLD is not given then elements of WORLD which defaults to the universe.
 Upon backtracking gives more possibilities."))
  ((apropos ?predicator ?substring . ?world-worlds)
   (predicator ?predicator . ?world-worlds)
   (lisp-predicate (string-search '?substring (string '?predicator)))))


(define-predicate print-definition
  (:options
     (:argument-list (predicator &optional world worlds))
     (:documentation
      "prints the definition of PREDICATOR found in WORLD which is a member
 of WORLDS.  Only those options of the definition that differ from the
 current default are displayed. Upon backtracking gives more possibilities."))
  ((print-definition ?predicator . ?world-worlds)
   (definition (define-predicate ? ?all-options . ?body)
	       ?predicator . ?world-worlds)
   (bag-of ?options ?option
	   (member ?option ?all-options) (cannot-prove (option ?option)))
   (cases ((= ?options (:options))
	   (lisp-command (pprint '(define-predicate ?predicator . ?body))))
	  ((lisp-command (pprint '(define-predicate ?predicator ?options . ?body)))))))

(defprop define-predicate si:grind-predicate si:grind-macro)

SI:
(DEFUN GRIND-PREDICATE (EXP LOC)
  (GTYO #/( LOC)
  (GRIND-ATOM (CAR EXP) GRIND-IO (LOCF (CAR EXP)))
  (GTYO #/ )
  (GRIND-ATOM (CADR EXP) GRIND-IO (LOCF (CAR EXP)))
  (grind-terpri)
  (GTYO #/ )
  (GRIND-REST-OF-LIST (CDDR EXP) (LOCF (CDR EXP)) 'GRIND-vertical-form))

(define-predicate documentation
  (:options
     (:argument-list (predicator &optional world worlds))
     (:documentation
       "prints documentation of PREDICATOR found in WORLD which is a member of WORLDS."))
  ((documentation ?predicator . ?world-worlds)
   (option (:documentation ?doc) ?predicator . ?world-worlds)
   (option (:argument-list ?arg-list) ?predicator . ?world-worlds)
   (option (:world ?world) ?predicator . ?world-worlds)
   (format t
	   "~& ~a is defined in world ~a.~% It expects to be called as~% ~a.~% ~a ~a"
	   ?predicator ?world (?predicator . ?arg-list) ?predicator ?doc)))

(define-predicate definition
  (:options
     (:argument-list (definition predicator &optional world worlds))
     (:documentation "unifies DEFINITION with the definition of PREDICATOR in WORLD.
 If WORLD is not given then with an element of WORLDS which defaults to the universe."))
  ((definition ?definition ?predicator . ?world-worlds)
   (either (= ?world-worlds (?world ?worlds))
	   (= ?world-worlds (?world))
	   (true))
   (predicator ?predicator ?world ?worlds)
   (lisp-value ?definition
	       (prolog-definition-of '?predicator '?world))))

(define-predicate remove-definition
  (:options
     (:argument-list (+predicator +world))
     (:documentation "removes the +PREDICATOR's definition from +WORLD."))
  ((remove-definition ?predicator ?world)
   (symbol ?predicator)
   (symbol ?world)
   (lisp-predicate (remove-the-definition '?predicator '?world))))

(defun remove-the-definition (predicator world)
  (cond ((definition-in-world predicator world)
	 (remove-from-world predicator world)
	 t)))

(define-predicate clause
  (:options
     (:argument-list (clause &optional world worlds))
     (:documentation "unifies CLAUSE with all relevant clauses in the WORLD.
 If no WORLD is given then members of WORLDS which defaults to the universe."))
  ((clause ((?predicator . ?arguments) . ?body) . ?world-or-worlds)
   (predicator ?predicator . ?world-or-worlds)
   (rules ?world-or-worlds
	  (() (universe ?universe) (member ?the-world ?universe))
	  ((?the-world))
	  ((?the-world ?universe) (member ?the-world ?universe)))
   (clauses ?clauses (?predicator . ?arguments) ?the-world)
   (member ((?predicator . ?arguments) . ?body) ?clauses))
  ((clause (?name (?predicator . ?arguments) . ?body) . ?world-or-worlds)
   (atomic ?name) ;;is really a name
   (predicator ?predicator . ?world-or-worlds)
   (rules ?world-or-worlds
	  (() (universe ?universe) (member ?the-world ?universe))
	  ((?the-world))
	  ((?the-world ?universe) (member ?the-world ?universe)))
   (clauses ?clauses (?predicator . ?arguments) ?the-world)
   (member (?name (?predicator . ?arguments) . ?body) ?clauses)))

(define-predicate clauses
  (:options
     (:argument-list (possible-clauses +predication &optional +world))
     (:documentation
       "unifies POSSIBLE-CLAUSES with those clauses which are found by
 indexing from +PREDICATION."))
  ((clauses ?possible-clauses ?predication)
   (clauses ?possible-clauses ?predication ()))
  ((clauses ?possible-clauses ?predication ?world)
   (lisp-value ?possible-clauses (possible-clauses-of '?predication '?world))))

(deffun possible-clauses-of (predication world)
  (cond ((consp predication)
	 (let ((definition
		 (cond ((null world)
			(current-definition (first predication) nil))
		       (t (definition-in-world (first predication) world)))))
	   (cond ((not (null definition))
		  (let* ((indexes (definition-indexes definition))
			 (clauses-in-world
			   (cond ((null indexes) (definition-clauses definition))
				 (t (apply-indexes
				      indexes
				      (rest1 predication)
				      (locf (definition-clauses definition)))))))
		    (cond ((null world)
			   (let ((options (definition-options definition)))
			     (selectq
			       (option-value ':if-another-definition options)
			       (:ignore clauses-in-world)
			       (:try-after
				(append
				  clauses-in-world
				  (let ((*universe*
					  (rest1
					    (memq (option-value ':world options)
						  *universe*))))
				    (possible-clauses-of predication world))))
			       (:try-before
				(append
				  (let ((*universe*
					  (rest1
					    (memq (option-value ':world options)
						  *universe*))))
				    (possible-clauses-of predication world))
				  clauses-in-world))
			       (otherwise clauses-in-world)))) ;;bad option value?
			  (t clauses-in-world)))))))
	((typep predication 'prolog-flavor)
	 (multiple-value-bind (new-predication instance-p)
	     (send predication ':ordinary-term)
	   (cond (instance-p nil)
		 (t (possible-clauses-of new-predication world)))))))

(deffun APPLY-INDEXES (indexes arguments1 CLAUSES-LOC &rest subsets)
  (cond ((null indexes)
	 (cond (subsets (APPLY 'INTERSECTION SUBSETS))
	       (t (CONTENTS CLAUSES-LOC))))
	(t (let* ((index (car indexes))
		  (key (funcall (index-key-finder index) arguments1)))
	     (cond ((value-cell-p key)
		    (lexpr-funcall 'APPLY-indexeS (cdr indexes) arguments1 CLAUSES-LOC subsets))
		   (t (let ((some-clauses (gethash key (index-table index))))
			(cond (some-clauses
			       (lexpr-funcall 'APPLY-indexeS (cdr indexes) arguments1 CLAUSES-LOC
					      (cons-by-length some-clauses
							      (length some-clauses)
							      subsets)))))))))))
