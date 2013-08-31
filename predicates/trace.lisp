;;; -*- Mode: Lisp; Package: Prolog; Base: 10; Options: ((World System)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;this is the LM-Prolog's trace facility

;;Stuff to control the default print format.

(defvar *trace-parameters* '(*print-escape* *print-base* *print-radix* *print-circle* *print-pretty*
					    *print-gensym* *print-array* *print-case* *print-level* *print-length*))



(defvar *trace-closure*
	(progv *trace-parameters* (mapcar 'symeval *trace-parameters*)
	  (closure *trace-parameters* #-lexical '%invoke #+lexical 'funcall)))

(defun choose-trace-parameters ()
       (funcall *trace-closure*
	(continuation (tv:choose-variable-values *trace-parameters*
						 ':label "Choose Trace Parameters"))))


(defun print-trace-doit (term)
  (funcall *trace-closure* (continuation (funcall 'write term))))


(define-predicate break
  (:options (:documentation "enters a recursive Prolog top loop."))
  ((break) (lisp-command (si:prolog-break))))

(define-predicate first-member
  :(options (compile-method open))
  ((first-member ?element ?list)
   (prove-once (member ?element ?list))))

(define-predicate trace
  :(options
     (argument-list (+predicator-or-predicators &rest +options))
     (documentation
       "traces each call to +PREDICATOR-OR-PREDICATORS if it is a symbol,
 or each of the elements of +PREDICATOR-OR-PREDICATORS if it is list.
 The currently supported options to trace are:

 (:PRINT-IF . ?PORT-NAMES) where the valid port names are
 :TRYING :SUCCEEDING :FAILING and :RE-TRYING the default is all four of them

 (:WHEN . ?PATTERNS) --- the tracing//stepping applies only if the call unifies
 with at least one of the ?PATTERNS 

 :STEP  --- enter step mode when the predicate is entered
	    this mode is self documenting (hit HELP for help)

 (:BEFORE ?PREDICATOR) --- ?PREDICATOR is called on the ?CALL upon entry
 (:AFTER ?PREDICATOR) ---- ?PREDICATOR is called on the ?CALL after entry

 (:WORLD ?WORLD) --- ?WORLD where the traced predicate is to live, 
		     defaults to PROLOG:TRACED-PREDICATES"))
  ((trace ?name-or-names . ?trace-options)
   (cases ((first-member (:world ?world) ?trace-options))
	  ((= ?world traced-predicates)))
   (bag-of ? ?
    (either (member ?predicator ?name-or-names)
	    (= ?predicator ?name-or-names))
    (either (untrace ?predicator) (true))
    (either (prove-once
	      (definition (define-predicate ? (:options . ?old-options) . ?)
			  ?predicator))
	    (and (format t "~%Warning from trace: ~s is not a predicator"
			 ?predicator)
		 (fail)))
    (remove ?options-1 (:compile-method . ?) ?old-options)
    (remove ?options-2 (:indexing-patterns . ?) ?options-1)
    (substitute ?new-options (:world ?old-world) (:world ?world) ?options-2 =)
    (trace-body ?body ?predicator ?trace-options ?old-world)
    (add-world ?world)
    (define-predicate ?predicator (:options . ?new-options)
      ?body))))

(define-predicate trace-body
  ((trace-body ((?predicator . ?arguments) . ?body) ?predicator ?options ?world)
   (= ?call (?predicator . ?arguments))
   (either (first-member (:print-if . ?ports) ?options)
	   (= ?ports :(trying failing succeeding re-trying)))
   (cases ((first-member :trying ?ports) (= ?trying "Trying:    "))
	  ((= ?trying ())))
   (cases ((first-member :failing ?ports) (= ?failing "Failing:   "))
	  ((= ?failing ())))
   (cases ((first-member :succeeding ?ports)
	   (= ?succeeding "Succeeding:"))
	  ((= ?succeeding ())))
   (cases ((first-member :re-trying ?ports) (= ?re-trying "Re trying: "))
	  ((= ?re-trying ())))
   (cases ((and (= ?trying ()) (= ?failing ()) (= ?succeeding ()) (= ?re-trying ()))
	   (= ?print-in ())
	   (= ?print-out ()))
	  ((= ?print-out
	      ((print-trace-out ?succeeding ?re-trying ?indentation ?level ?call)))
	   (= ?print-in
	      ((print-trace-in ?trying ?failing ?indentation ?level ?call)))))
   (cases ((first-member :step ?options)
	   (= ?try ((do-step-response ?call ?world))))
	  ((= ?try ((call ?call ?world)))))
   (cases ((first-member (:before ?before-predicate) ?options)
	   (= ?before ((?before-predicate ?call))))
	  ((= ?before ())))
   (cases ((first-member (:after ?after-predicate) ?options)
	   (= ?after ((?after-predicate ?call))))
	  ((= ?after ())))
   (append ?inner-body ?print-in ?before ?try ?after ?print-out)
   (cases ((first-member (:when . ?patterns) ?options)
	   (= ?body ((cases ((can-prove (member ?call ?patterns)) . ?inner-body)
			    ((call ?call ?world))))))
	  ((= ?body ?inner-body)))))

(define-predicate call-hook
  (:options (:deterministic :never)))

(define-predicate exit-hook
  (:options (:deterministic :never)))

(defun exit-hook-in-/:system-prover (cont)
  (let ((old-ancestors *ancestors*)
	(aloc (list-in-area *prolog-work-area* ':location (locf *ancestors*))))
    (trail (continuation (funcall 'lisp-value-reset aloc old-ancestors)))
    (pop *ancestors*)
    (invoke cont)))

(defun call-hook-in-/:system-prover (cont goal level indent)
  (let ((old-history *history*)
	(old-ancestors *ancestors*)
	(hloc (list-in-area *prolog-work-area* ':location (locf *history*)))
	(aloc (list-in-area *prolog-work-area* ':location (locf *ancestors*)))
	(tag (%cell0)))
    (unify level (length old-history))
    (unify indent (min 10 (1+ (length old-ancestors))))
    (trail (continuation (funcall 'lisp-value-reset hloc old-history)))
    (trail (continuation (funcall 'lisp-value-reset aloc old-ancestors)))
    (setq *history*
	  (prolog-cons (prolog-list level goal tag) *history*)
	  *ancestors*
	  (prolog-cons (car *history*) *ancestors*))
    (do ((mark *trail* *trail*))
	((*catch tag (invoke cont)) t)
      (untrail mark))))

(define-predicate print-trace-in 
  ((print-trace-in ?trying ?failing ?indent ?level ?goal)
   (call-hook ?goal ?level ?indent)
   (or (cases ((= ?trying ()))
	      ((format t "~%~VT(~D)~A " ?indent ?level ?trying)
	       (lisp-command (print-trace-doit '?goal) :dont-invoke)))
       (cases ((= ?failing ())
	       (cut)
	       (false))
	      ((format t "~%~VT(~D)~A " ?indent ?level ?failing)
	       (lisp-command (print-trace-doit '?goal) :dont-invoke)
	       (cut)
	       (false))))))

(define-predicate print-trace-out
  ((print-trace-out ?trying ?failing ?indent ?level ?goal)
   (exit-hook)
   (or (cases ((= ?trying ()))
	      ((format t "~%~VT(~D)~A " ?indent ?level ?trying)
	       (lisp-command (print-trace-doit '?goal) :dont-invoke)))
       (cases ((= ?failing ())
	       (false))
	      ((format t "~%~VT(~D)~A " ?indent ?level ?failing)
	       (lisp-command (print-trace-doit '?goal) :dont-invoke)
	       (false))))))


(defun step-response-help (stream &rest ignore)
  (format stream "~%You are in the stepper.
Type ~:C, ~:C or ~C to step through everything (to CREEP),
Type ~:C or ~C to continue (LEAP),
Type ~:C or ~C to prove the current goal without any tracing (SKIP),
Type ~:C to CLEAR SCREEN,
Type ~C for MENU of display parameters,
Type ~C to PRINT goal,
Type ~C to GRIND goal,
Type ~C to list ANCESTORS,
Type ~C to display a BACKTRACE of ancestors,
Type ~C to RETRY a goal,
Type ~C to cause the current goal to be FALSE,
Type ~C to cause the current goal to be TRUE,
Type ~C to give the ANSWER,
Type ~C to EDIT definition,
Type ~C to ABORT query,
Type ~C to BREAK to a Prolog Listener."
	  #\SPACE #\CR #/C #\LINE #/L #\ALTMODE #/S #\CLEAR-SCREEN #/M #/P #/G #/A #/B #/R #/F #/T #/= #/.
	  #\ABORT #\BREAK))

(DEFFUN step-response (call world)
  (let ((response
	  (FQUERY '(:choices
		    (((skip "Skip.") #\ALTMODE #/S)
		     ((break "Break.") #\BREAK)
		     (refresh #\CLEAR-SCREEN)
		     ((leap "Leap.") #\LINE #/L)
		     ((creep "Creep.") #\SPACE #\CR #/C)
		     ((menu "Menu.") #/M)
		     ((false "False.") #/F)
		     ((true "True.") #/T)
		     ((ancestors "Ancestors: ") #/A)
		     ((verbose-ancestors "Backtrace of Ancestors.") #/B)
		     ((retry "Retry.") #/R)
		     ((print "Print.") #/P)
		     ((grind "Grind.") #/G)
		     ((accept "Accept.") #/=)
		     ((edit "Edit.") #/.))
		    :list-choices nil
		    :fresh-line nil
		    :help-function
		    step-response-help)
		  " ? ")))
    (selectq response
      (refresh (send standard-output ':clear-screen)
	       (step-response call world))
      (ancestors
       (dolist (a *ancestors*) (prin1-then-space (car a)))
       (terpri)
       (step-response call world))
      (verbose-ancestors
       (dolist (a *ancestors*)
	 (format t "~% (~d) " (car a))
	 (print-trace-doit (lisp-form-1 (cadr a) ':dont-invoke)))
       (terpri)
       (step-response call world))
      (retry (let ((item (goal-prompt call)))
	       (cond (item (*throw (third item) nil))
		     (t (step-response call world)))))
      (menu (choose-trace-parameters)
	    (step-response call world))
      (print (let ((item (goal-prompt call)))
	       (and item
		    (let ((*print-pretty* nil))
		      (print (lisp-form (second item) ':dont-invoke)))))
	     (step-response call world))
      (grind (let ((item (goal-prompt call)))
	       (and item
		    (let ((*print-pretty* nil)) 
		      (pprint (lisp-form (second item) ':dont-invoke)))))
	     (step-response call world))
      (break (si:prolog-break)
	     (step-response call world))
      (accept (format t "~%Enter a term to unify with the current goal: ")
	      (prolog-cons 'answer (PARSE-TERM (read))))
      (edit (ed (prolog-list 'si:functions-to-be-edited
			     (prolog-db-symbol (car call) world 'prover)
			     (car call)))
	    (step-response call world))
      (t response))))

(defun goal-prompt (goal)
 (catch-error-restart ((error si:abort) "Back to Step Response.")
  (let (level item)
    (FORMAT T "~%Which goal, ~C for current, ~C to cancel: " #\end #\abort)
    (cond ((and (= #\end (setq level (send standard-input ':tyi)))
		(assq-goal goal *history*)))
	  ((progn (send standard-input ':untyi level) nil))
	  ((NOT (NUMBERP (SETQ LEVEL (READ)))) (SI:BEEP) (GOAL-PROMPT goal))
	  ((NOT (SETQ ITEM (ASSQ LEVEL *HISTORY*))) (SI:BEEP) (GOAL-PROMPT goal))
	  (T ITEM)))))


(defun assq-goal (goal hist)
  (cond ((null hist) nil)
	((eq goal (second (first hist))) (first hist))
	(t (assq-goal goal (rest1 hist)))))


(define-predicate untrace
  :(options
     (argument-list (&optional predicator))
     (documentation
       "removes a trace from PREDICATOR if given, otherwise removes all traces."))
  ((untrace ?predicator)
   (predicator ?predicator traced-predicates)
   (remove-definition ?predicator traced-predicates))
  ((untrace) ;;all
   (remove-world traced-predicates)
   (bag-of ? ?
     (predicator ?predicator traced-predicates)
     (untrace ?predicator))))
	  
(define-predicate untrace-query
  :(options
     (documentation
       "queries the user for each traced predicate whether it should be untraced."))
  ((untrace-query)
   (bag-of ? ?
    (predicator ?predicator traced-predicates)
    (y-or-n "~%Untrace ~s? " ?predicator)
    (untrace ?predicator))))

(define-predicate who-state
  :(options (argument-list (+label))
	    (documentation "displays +LABEL on the run state part of the who line,
 upon backtracking the original state is restored."))
  ((who-state ?label)
   (lisp-value ?old-label (si:process-wait-whostate current-process) )
   (unwind-protect
     (lisp-command (set-who-state '?label))
     (lisp-command (set-who-state '?old-label)))))

(deffun set-who-state (label)
  (setf (process-whostate current-process) (string label))
  (tv:who-line-run-state-update))

;;; The Step facility, by Mats Carlsson.


(defun get-p-and-world (p world)
  (and (unify p (definition-predicator *definition*))
       (unify world (option-value ':world (definition-options *definition*)))))

;;We get here with stepping turned on and with
;;*definition* closure bound to the thing we really want to call.
(define-predicate do-step
  ((do-step . ?args)
   (lisp-command (get-p-and-world '?p '?world) )
   (= ?call (?p . ?args))
   (unwind-protect
     (lisp-command (step-off))
     (lisp-command (step-on)))
   (print-trace-in "Trying:    " "Failing:   " ?x ?y ?call)
   (do-step-response ?call ?world)
   (print-trace-out "Succeeding:" "Re trying: " ?x ?y ?call)
   (unwind-protect
     (lisp-command (step-on))
     (lisp-command (step-off)))))

(define-predicate do-step-response
  ((do-step-response ?call ?world)
   (lisp-value ?response (step-response '?call '?world))
   (RULES ?RESPONSE
	  (CREEP (step ?call ?world))
	  (LEAP (call ?call ?world))
	  (SKIP (without-world traced-predicates (call ?call ?world)))
	  (TRUE)
	  ((ANSWER . ?call)))))

(define-predicate step
  (:options
    (:argument-list (+call &optional +world))
    (:documentation "executes CALL with global stepping turned on."))
  ((step ?call)
   (unwind-protect
     (lisp-command (step-on))
     (lisp-command (step-off)))
   ?call
   (unwind-protect
     (lisp-command (step-off))
     (lisp-command (step-on))))
  ((step ?call ?world)
   (unwind-protect
     (lisp-command (step-on))
     (lisp-command (step-off)))
   (call ?call ?world)
   (unwind-protect
     (lisp-command (step-off))
     (lisp-command (step-on)))))
