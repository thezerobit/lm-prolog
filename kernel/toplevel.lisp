;;; -*- Mode:LISP; Package:PROLOG; Base:10 -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;-------- A completely new toplevel.

(defconst *prolog-help*
	  "You are typing input to ~A.
The syntax of LM-Prolog is:
/(define-predicate <predicator> <clause> <clause> ...) where:
A clause is a cons of a head and a list of goals.
Heads and goals are predications.
A predication is a cons of a symbol and a term.
A term is any s-expression.
A variable is a symbol whose name begins with a single ?.

~C ~:@C takes you to a Prolog Listener.
Lisp forms can be entered if preceded by comma (,).
M-X Zlog Mode in Zwei converts your buffer into a Prolog interaction buffer.

LM-Prolog idioms are available in the PUSER: package.

Type (option (:documentation ?d) ?predicator) to get documentation on predicates.
Try running (demos).")


TV:
(define-rh-command rh-com-help-for-prolog (#\super-help) (ignore)
  (RH-DISPLAY-INFO
    (FORMAT SELF prolog:*prolog-help* SELF #\SYSTEM #\GREEK-P)))

TV:
(defvar rh-command-alist-prolog (copytree rh-command-alist))

;;; These typically have to be changed for new releases.

TV:
(psetq rh-command-alist-prolog rh-command-alist rh-command-alist rh-command-alist-prolog)

TV:
(DEFINE-RH-COMMAND RH-COM-ARGUMENT-LIST-for-prolog (#/CONTROL-SHIFT-A) (ignore)
  (LET ((FN (RH-GET-FUNCTION)))
    (cond ((null fn) (send self ':beep))
	  ((RH-DISPLAY-INFO
	     (cond ((zwei:generally-defined fn)
		    (ZWEI:PRINT-ARGLIST fn SELF))
		   (T
		    (FORMAT SELF "Can't find a definition for ~S." FN))))))))

TV:
(DEFINE-RH-COMMAND RH-COM-DOCUMENTATION-for-prolog (#/CONTROL-SHIFT-D) (ignore)
  (LET ((FN (RH-GET-FUNCTION)))
    (cond ((null fn) (send self ':beep))
	  ((RH-DISPLAY-INFO
	     (cond ((zwei:generally-defined fn)
		    (ZWEI:PRINT-ARGLIST fn SELF)
		    (TERPRI SELF)
		    (SEND SELF :STRING-OUT (zwei:general-documentation fn)))
		   (t
		    (FORMAT SELF "Can't find a definition for ~S." FN))))))))

TV:
(psetq rh-command-alist-prolog rh-command-alist rh-command-alist rh-command-alist-prolog)

;;;Read table hackery.


(defun source-variable-read-macro (stream arg)
  (let ((flavor-name 'source-variable)
	(c (send stream ':tyi)))
    (send stream ':untyi c)
    (cond ((= c #/?)
	   (tyi stream)			   ;echo properly
	   (setq flavor-name 'source-ro-variable c (send stream ':tyi))
	   (send stream ':untyi c)))
    (values				   ;force one value from read macro!
      (cond ((alphanumericp c)
	     (make-instance flavor-name ':name (si:read-recursive stream)))
	    (t (make-instance flavor-name ':name ':unbound))))))

(defun install-variable-syntax (&optional (rt *readtable*))
  (set-macro-character #/? 'source-variable-read-macro nil rt))

(mapc 'install-variable-syntax si:*all-readtables*)

;Above doesn't seem to catch them all.
(install-variable-syntax si:standard-readtable)
(install-variable-syntax si:common-lisp-readtable)
(install-variable-syntax *readtable*)

(defvar *lisp-readtable* *readtable*)

(defvar *prolog-readtable* (si:find-readtable-named "standard LM-Prolog" t))

(set-macro-character #/, 'comma-read-macro nil *prolog-readtable*)

(defun comma-read-macro (stream arg)
  (cond (si:**BACKQUOTE-REPEAT-VARIABLE-LISTS**	;we're inside a backquote
	 (si:xr-comma-macro stream arg))
	((let ((*readtable* *lisp-readtable*))
	 (prolog-list 'lisp-command
			(prolog-list 'print-lisp-values
				     (prolog-list 'quote (si:read-recursive stream))))))))


(defun print-lisp-values (form)			;Form was parsed, now unparse it!
  (dolist (v (multiple-value-list (eval (lisp-form-1 form ':dont-invoke))))
    (print-top-level v)))


;; These (and a few more) are maintained per window.

(defvar *mark* ':unbound "The point to which to reset the trail for this level.")
(defvar *mark-stack* ':unbound "A stack of trail pointers for recursive levels.")

;; For the trace facility.

(defvar *history* () "The currently active goals that are being traced.")

(defvar *ancestors* () "The currently active ancestors that are being traced.")

(defvar *step* nil "Governs single stepping of predicates.")

(defun step-on ()
  (setq *step* t *universe* (cons (car *universe*) (cdr *universe*))))

(defun step-off ()
  (setq *step* nil))

(defun reset-trace ()
  (step-off)
  (setq *history* () *ancestors* ()))
       

(defun reset-prolog ()
  #-symbolics (array-initialize *original-trail-array* nil)
  #+symbolics (fillarray *original-trail-array* '(nil))
  (setq *prolog-work-area* *single-prolog-work-area*
	*cut-tag* 'top-level-cut-tag
	*conses-alist* ()
	*vector* *original-vector*
	*trail-array* *original-trail-array*)
  (link-*trail*-count)
  (setq *trail* 0)
  #+PROLOG-MICRO-CODE (LOAD-MICROCODE) ;;This wants things above to have decent values...
  (set-circularity-mode *circularity-mode*) ;;After above since it touches processor memories
  (cond ((not (universe-ok *universe*))
	 (format t "There is something wrong with the universe ~S, being reset to (:user :system)"
		 *universe*)
	 (set-universe '(:user :system))))
  (with-trail *top-level-trail-array* (untrail 0))
  (reset-trace)
  )


(add-initialization
  "Re-setting the Prolog Top Level"
  '(reset-prolog)
  '(:warm))

(DEFUN PRINT-TOP-LEVEL (X)
  (TERPRI)
  (FUNCALL (OR PRIN1 #'PRIN1) X))


;;; Documented interface from Lisp.

(defflavor prolog-query
           (term trail table return-trail-p mark proof-stream work-area)
           ()
  :initable-instance-variables)

(defmethod (prolog-query :flush) ()
  (let ((*prolog-work-area* work-area)
	(*symbol-table* table))
    (cond (trail
           (with-trail trail
	     (setq proof-stream (progn (untrail mark) nil))
	     (deallocate-resource 'symbol-table table))
           (cond (return-trail-p (deallocate-a-trail trail)))
           (setq term nil trail nil table nil proof-stream nil)	   ;for GC
	   ))))

(defmethod (prolog-query :next-answer) ()
  (cond ((null proof-stream) nil)
        (t (let ((*prolog-work-area* work-area)
		 (*symbol-table* table))
	     (*catch *cut-tag*
	       (with-trail trail
		 (setq proof-stream (invoke proof-stream))))
	     (cond ((null proof-stream) nil)
		   (t (let ((*prolog-work-area* default-cons-area))
			(values (lisp-form (%dereference term) ':invoke) t))))))))

(defun query-once (lisp-predication
                   &optional &key
                   (lisp-term lisp-predication))
  (let ((stream
          (make-query lisp-predication
		      ':lisp-term lisp-term
		      ':trail *trail-array*
		      ':mark *trail*
		      ':area *prolog-work-area*
		      ':deterministic t)))
    (multiple-value-bind (value succeeded-p) (send stream ':next-answer)
      (send stream ':flush)
      (values value succeeded-p))))

(defun make-query (lisp-predication
		   &optional &key
		   (lisp-term lisp-predication)
		   (size 500.)
		   (TRAIL)
		   (mark 0)
		   (area default-cons-area)
		   (deterministic nil))

  (cond ((atom lisp-predication)
	 (prolog-error ':atom-as-predication
	  "~s, which is not a list, given as a predication."
	  lisp-predication)))

  (let* ((*prolog-work-area* area)
         (*symbol-table* (allocate-resource 'symbol-table))
	 (old-trail-p trail))
    (with-trail (or old-trail-p (allocate-resource 'trail size))
      (let* ((predication (parse-term lisp-predication))
	     (term (cond ((eq lisp-predication lisp-term) predication)
			 (t (parse-term lisp-term))))
	     (definition (current-definition (first predication)))
	     (prover (definition-prover definition))
	     (proof-stream
	       (cond ((or deterministic (definition-deterministic definition))
		      ;;important optimization
		      (continuation
			(lexpr-funcall
			  prover
			  (continuation (continuation (false)))
			  (rest1 predication))))
		     (t (let* ((csg si:%current-stack-group)
			       (continuation
				 (continuation (funcall #'stack-group-resume csg t)))
			       (coroutine
				 (allocate-a-coroutine
				   prover
				   continuation
				   (rest1 predication))))
			  (continuation (funcall #'resume coroutine)))))))
	(make-instance-in-area area 'prolog-query
			       ':term term
			       ':trail *trail-array*
			       ':mark mark
			       ':work-area area
			       ':table *symbol-table*
			       ':return-trail-p (not old-trail-p)
			       ':proof-stream proof-stream)))))

(defun resume (sg)
  (cond ((si:sg-resumable-p sg) ;;can be in a bad state due to [abort]
	 (detach sg (funcall sg nil))))) ;;NIL will force coroutine to backtrack

(deffun detach (sg msg)
  (cond ;;This is for fancy inter-stack-group communication that was used once with ZTOP.
;        ((and #-symbolics ( sys:sg-state-exhausted (sys:sg-current-state sg))
;              #+symbolics (zerop (si:sg-exhausted-bit sg))
;              (consp msg))
;         (detach sg
;          (funcall sg
;            (multiple-value-list ;;Some methods m-v-return, e.g. CURSORPOS
;              (cond ((eq ':rubout-handler (second msg))
;                     (funcall (symeval (first msg))
;                              (second msg)
;                              (third msg)
;                              (fourth msg)
;                              (symeval (first msg))
;                              (nth 5 msg)))
;                    (t (apply (symeval (first msg)) (rest1 msg))))))))
        ((null msg) nil)
        (t (continuation (funcall #'resume sg)))))


(defvar *top-level-regpdl-size* 20000.) ;;for user customizations...

(defvar *coroutine-regpdl-size* #o10000)

(defvar *top-level-specpdl-size* 2000.)

(defvar *coroutine-specpdl-size* #o1000)

(defresource coroutine  (reg spec)
  :constructor
  (list (make-stack-group 'prolog-coroutine
                          ':regular-pdl-size reg
			  ':special-pdl-size spec)
        ;;the following is the *vector* of the process
	;;it is long enough for 4 recursive entries to %unify-term-with-template
	;;this happens currently only when unifying constraints or clauses
        (make-list 256. ':area permanent-storage-area)))

(defun coroutine-closure-function #.*variables-shared-between-top-level-stack-groups*
  (establish-condition-handlers
    (*catch *cut-tag*
      (catch-error-restart
	((sys:abort error) "Terminate and return to Prolog top level")
	(with-trail *trail-array* (lexpr-funcall function continuation arglist))))))

(defun allocate-a-coroutine (function continuation arglist &optional top-level-p)
  (let (stack-group-and-vector)
    (unwind-protect
	(progn
	  (setq stack-group-and-vector
		(cond (top-level-p
		       (allocate-resource 'coroutine
					  *top-level-regpdl-size*
					  *top-level-specpdl-size*))
		      (t (allocate-resource 'coroutine
					    *coroutine-regpdl-size*
					    *coroutine-specpdl-size*))))
	  (let* ((stack-group (first stack-group-and-vector))
		 (*vector* (second stack-group-and-vector)))
	    (stack-group-preset stack-group #'coroutine-closure-function
				. #.*variables-shared-between-top-level-stack-groups*)))
      (and stack-group-and-vector
	   (trail
	     (continuation
	       (funcall #'deallocate-a-coroutine stack-group-and-vector)))))))

(defun deallocate-a-coroutine (stack-group-and-vector)
  #-symbolics
  (eh:sg-unwind (car stack-group-and-vector) t eh:%current-stack-group nil
		;;Using %current-stack-group or #'stack-group-return as "action" doesnt win!
		#'(lambda (x) (stack-group-resume x nil))
		'eh:free)
  #+symbolics
  (dbg:unwind-sg (car stack-group-and-vector) #'(lambda (x) (stack-group-resume x nil))
		dbg:%current-stack-group nil)
  (deallocate-resource 'coroutine stack-group-and-vector))

;;and here is LM-Prolog's DWIM facility

(defflavor undefined-predicate-error (predicator worlds) (error)
  :gettable-instance-variables
  :initable-instance-variables)

(defmethod (undefined-predicate-error :user-proceed-types) (proceed-types)
  ;;Force them to appear in preferred order.
  (list*-in-area *prolog-work-area* ':no-action ':new-value ':fail (cdddr proceed-types)))

#-symbolics
(progn 'compile
(defmethod (undefined-predicate-error :case :proceed-asking-user :no-action)
	   (continuation read-object-function)
  "Proceeds, using current definition if valid, or reading new predicator."
  (let ((def (find-and-cache-first-definition (definitions predicator) worlds)))
    (cond (def (send continuation ':no-action))
	  (t (send self ':proceed-asking-user ':new-value
		   continuation read-object-function)))))

(defmethod (undefined-predicate-error :case :proceed-asking-user :new-value)
	   (continuation read-object-function)
  "Reads a new predicator to use instead."
  (send continuation ':new-value
	(send read-object-function ':read "~&Predicator to use instead: ")))

(defmethod (undefined-predicate-error :case :proceed-asking-user :fail)
	   (continuation ignore)
  "Make the call fail."
  (send continuation ':fail))

(defsignal undefined-predicate undefined-predicate-error (predicator worlds)
  "Signaled when an undefined predicate is invoked."
  ':predicator predicator ':worlds worlds)

)

#+symbolics
(progn 'compile
(defmethod (undefined-predicate-error :report) (stream)
  (format stream "The predicate ~S is undefined." predicator))

(defmethod (undefined-predicate-error :case :proceed :no-action) ()
  "Proceeds, using current definition if valid, or reading new predicator."
  (let ((def (find-and-cache-first-definition (definitions predicator) worlds)))
    (cond (def ':no-action)
	  (t (send self ':proceed ':new-value)))))

(defmethod (undefined-predicate-error :case :proceed :new-value) ()
  "Reads a new predicator to use instead."
  (values ':new-value (prompt-and-read ':expression "~&Predicator to use instead: ")))

(defmethod (undefined-predicate-error :case :proceed :fail) ()
  "Make the call fail."
  ':fail)
)

(defun undefined-predicate (predicator worlds)
  (declare (special predicator)) ;;for closure's sake
  (cond ((ask-about-each-world predicator
                               (mapcar #'first (rest1 (definitions predicator)))))
        ((*catch 'package-map-tag
           (#-symbolics si:map-over-lookalike-symbols
            #+symbolics dbg:map-over-lookalike-symbols
            (string predicator)
            pkg-global-package
            #'ask-about-predicator-in-package
            predicator worlds)))
	((eq *undefined-predicate-mode* ':fail) (current-definition 'false))
	(t (multiple-value-bind (action new-name)
	       #-symbolics
	     (let ((cc (make-condition 'undefined-predicate
				       "The predicate ~S is undefined." predicator worlds)))
	       (signal-condition cc (send cc ':proceed-asking-user ':which-operations)))
	     ;Stopped working in Release 3.0:
	     ;(signal 'undefined-predicate
	     ;"The predicate ~S is undefined." predicator worlds)
	     #+symbolics
	     (signal 'undefined-predicate-error ':predicator predicator ':worlds worlds)
	     (selectq action
	       (:no-action
		(find-and-cache-first-definition (definitions predicator) worlds predicator))
	       (:new-value
		(find-and-cache-first-definition (definitions new-name) worlds new-name))
	       (:fail
		(current-definition 'false)))))))

(defun ask-about-predicator-help (query-io &rest ignore)
  (format query-io
	  "~%Type /"y/" to continue with new definition,
Type /"n/" to continue to search for definition,
Or type /"g/" to continue with new definition and go to the package"))

(defun ask-about-predicator-in-package (symbol predicator worlds)
  (let ((definition (current-definition symbol nil worlds)))
    (and definition
         (selectq
           (fquery '(:choices (((yes "Yes") #/Y #/T #/y #/t #\SP)
                               ((no "No") #/n #/N #\Rubout)
                               ((go-to-package "Go to Package") #/g))
                     :help-function ask-abount-predicator-help)
                   "~s is not defined in the current universe, but ~s is.  
Use ~s instead? "
                   predicator symbol symbol)
           (yes (*throw 'package-map-tag definition))
           (no nil)
           (go-to-package (pkg-goto (symbol-package symbol))
                          (*throw 'package-map-tag definition))))))

(defun ask-about-world-help (query-io &rest ignore)
  (format query-io "~%Type /"y/" to continue with new definition,
Type /"n/" to continue to search for definition,
Or type /"a/" to continue with new definition and add world to the universe."))

(deffun ask-about-each-world (predicator defined-in-worlds)
  (cond ((memq (first defined-in-worlds) *universe*)
	 (cond ((y-or-n-p (prolog-string "Use definition of ~S in ~S? "
					 predicator
					 (first defined-in-worlds)))
		(definition-in-world predicator (first defined-in-worlds)))
	       ((ask-about-each-world predicator (rest1 defined-in-worlds)))))
	(defined-in-worlds
         (selectq
           (fquery '(:choices (((yes "Yes") #/Y #/T #/y #/t #\SP)
                               ((no "No") #/n #/N #\Rubout)
                               ((add "Add World") #/a))
                     :help-function ask-about-world-help)
		   "~s is not defined in the current universe, but is in ~s.  
Use definition in ~s? "
                   predicator
                   (first defined-in-worlds)
                   (first defined-in-worlds))
           (yes (definition-in-world predicator (first defined-in-worlds)))
           (no (ask-about-each-world predicator (rest1 defined-in-worlds)))
           (add (setq *universe*
                      (cons (first defined-in-worlds)
                            (delq (first defined-in-worlds) *universe*)))
                (definition-in-world predicator (first defined-in-worlds)))))))

;;; Prolog Listener windows and System-Greek-P.

(DEFCONST PROLOG-TOP-LEVEL-INSIDE-EVAL nil
  "Bound to T while within PROVE inside the top-level loop.")

(DEFFLAVOR PROLOG-LISTENER-MIXIN-INTERNAL (PROLOG-LISTENER-PACKAGE) (TV:PROCESS-MIXIN TV:FULL-SCREEN-HACK-MIXIN)
  (:DOCUMENTATION :SPECIAL-PURPOSE "An actual PROLOG window
Includes a process that will run the PROLOG top level read-eval-print loop.
Use this rather than PROLOG-LISTENER-MIXIN when you want to be invisible to the System-Greek-P key."))

(DEFMETHOD (PROLOG-LISTENER-MIXIN-INTERNAL :PACKAGE) ()
  (IF (VARIABLE-BOUNDP PROLOG-LISTENER-PACKAGE) PROLOG-LISTENER-PACKAGE))

(DEFMETHOD (PROLOG-LISTENER-MIXIN-INTERNAL :SET-PACKAGE) (PKG)
  (SETQ PROLOG-LISTENER-PACKAGE (PKG-FIND-PACKAGE PKG)))

(DEFMETHOD (PROLOG-LISTENER-MIXIN-INTERNAL :BEFORE :INIT) (IGNORE)
  (OR tv:PROCESS (SETQ tv:PROCESS '(PROLOG-TOP-LEVEL1 :REGULAR-PDL-SIZE 40000
						      :SPECIAL-PDL-SIZE 4000))))

(DEFFLAVOR PROLOG-LISTENER-MIXIN () (PROLOG-LISTENER-MIXIN-INTERNAL)
  (:DOCUMENTATION :SPECIAL-PURPOSE "An actual PROLOG window
Includes a process that will run the PROLOG top level read-eval-print loop.
Use this when you want to be visible to the System-Greek-P key."))


(DEFFLAVOR PROLOG-LISTENER () (TV:NOTIFICATION-MIXIN PROLOG-LISTENER-MIXIN TV:WINDOW)
  (:DEFAULT-INIT-PLIST :SAVE-BITS T)
  (:DOCUMENTATION :COMBINATION "Normal PROLOG window"))

(DEFMETHOD (PROLOG-LISTENER :PROLOG-LISTENER-P) ()
  (IF (SYMEVAL-IN-STACK-GROUP 'PROLOG-TOP-LEVEL-INSIDE-EVAL (PROCESS-STACK-GROUP tv:PROCESS))
      ':BUSY
    ':IDLE))

(DEFUN IDLE-PROLOG-LISTENER (&OPTIONAL (SUPERIOR tv:DEFAULT-SCREEN)
			   &AUX LL (FULL-SCREEN (MULTIPLE-VALUE-LIST
						  (SEND SUPERIOR ':INSIDE-SIZE))))
  "Find a PROLOG Listener that's not in use, and is the full size of the specified
superior.   Creates one if none is available."
  (SETQ LL (DOLIST (I (tv:SHEET-INFERIORS SUPERIOR))
	     (AND (EQ (SEND I ':PROLOG-LISTENER-P) ':IDLE)
		  (EQUAL FULL-SCREEN (MULTIPLE-VALUE-LIST (SEND I ':SIZE)))
		  (RETURN I))))
  (OR LL (tv:MAKE-WINDOW 'PROLOG-LISTENER ':SUPERIOR SUPERIOR)))

(DEFUN PROLOG-TOP-LEVEL1 (*TERMINAL-IO* &OPTIONAL (TOP-LEVEL-P T) &AUX OLD-PACKAGE W-PKG)
  "Read-eval-print loop used by PROLOG listeners.
*TERMINAL-IO* is the stream with which to read and print."
  (LET ((*PACKAGE* (pkg-find-package ':PUSER)))
    (FORMAT T "~&;Reading~:[~; at top level~]~@[ in ~A~]."
	      TOP-LEVEL-P (SEND-IF-HANDLES *TERMINAL-IO* :NAME))
    (let ((*cut-tag* 'top-level-cut-tag)
	  (*conses-alist* ())
	  (*vector* *original-vector*)
	  (*step* nil)
	  (*history* nil)
	  (*ancestors* nil)
	  (*definition* nil)
	  (*mark* 0)
	  (*mark-stack* ())
	  (*prolog-work-area* *single-prolog-work-area*)
	  
	  (tv:KBD-INTERCEPTED-CHARACTERS
	    (cons '(#/BREAK tv:KBD-INTERCEPT-prolog-BREAK)
		  tv:KBD-INTERCEPTED-CHARACTERS))
	  (tv:rh-command-alist tv:rh-command-alist-prolog)
	  (*READTABLE* *prolog-readtable*)
	  (LAST-TIME-READTABLE NIL)
	  THROW-FLAG)			   ;Gets non-NIL if throw to COMMAND-LEVEL (e.g. quitting from an error)

	(using-resource (*symbol-table* symbol-table)
	  (using-resource (*trail-array* trail 10000.)
	    (do ()
		(nil)
	      ;; If *PACKAGE* has changed, set OLD-PACKAGE and tell our window.
	      ;; Conversely, if the window's package has changed, change ours.
	      ;; The first iteration, we always copy from the window.
	      (COND ((NOT (VARIABLE-BOUNDP *PACKAGE*)))
		    ((EQ *TERMINAL-IO* si:COLD-LOAD-STREAM))
		    ;; User set the package during previous iteration of DO
		    ;; => tell the window about it.
		    ((AND OLD-PACKAGE (NEQ *PACKAGE* OLD-PACKAGE))
		     (SEND-IF-HANDLES *TERMINAL-IO* :SET-PACKAGE *PACKAGE*)
		     (SETQ OLD-PACKAGE *PACKAGE*))
		    ;; Window's package has been changed, or first iteration through DO,
		    ;; => set our package to the window's -- if the window has one.
		    ((SETQ W-PKG (SEND-IF-HANDLES *TERMINAL-IO* :PACKAGE))
		     (AND (NEQ W-PKG *PACKAGE*)
			  (SETQ *PACKAGE* W-PKG))
		     (SETQ OLD-PACKAGE *PACKAGE*))
		    ;; First time ever for this window => set window's package
		    ;; to the global value of *PACKAGE*.
		    ((NULL OLD-PACKAGE)
		     (SETQ OLD-PACKAGE *PACKAGE*)
		     (SEND-IF-HANDLES *TERMINAL-IO* :SET-PACKAGE *PACKAGE*)))
	      (si:CHECK-FOR-READTABLE-CHANGE LAST-TIME-READTABLE)
	      (SETQ LAST-TIME-READTABLE *READTABLE*)
	      (SETQ THROW-FLAG T)
	      (CATCH-ERROR-RESTART ((SYS:ABORT DBG:DEBUGGER-CONDITION) "Return to top level in ~A."
				    (OR (SEND-IF-HANDLES *TERMINAL-IO* :NAME) "current process."))
		(TERPRI)
		(SETQ - (tv:READ-FOR-TOP-LEVEL))
		(LET ((PROLOG-TOP-LEVEL-INSIDE-EVAL T))
		  (prolog-top-level-prove -))
		(SETQ THROW-FLAG NIL))
	      (WHEN THROW-FLAG
		;; Inform user of return to top level.
		(FORMAT T "~&;Back to top level~@[ in ~A~]."
			(SEND-IF-HANDLES *TERMINAL-IO* :NAME)))))))))

(TV:ADD-SYSTEM-KEY #\GREEK-P 'PROLOG-LISTENER-MIXIN "LM-Prolog" 'PROLOG-LISTENER)

;;; These macros are useful in a number of applications

;;This is the body of the top-level loop.
;;It converts the Lisp form just read into a Prolog structure
;;and "interns" the variables in the predication.
;;It binds the variables to their current values 
;;so that upon abnormal return they are restored

(defun prolog-top-level-prove (predication)
  (ESTABLISH-CONDITION-HANDLERS
    (with-trail *trail-array*
      (cond (*mark*
	     (with-who-line "Untrail" (untrail *mark*)))
	    (t (setq *mark* *trail*)))
      (prolog-top-level-prove-body predication))))


(defun top-level-continuation (cells &optional no-query)
  (mapc 'funcall cells (circular-list ':print-binding))
  (cond (no-query (format t "~%Yes.") t)
	(t (y-or-n-p "Yes, enough solutions? "))))

(deffun source-variables-in (term sofar)
  (cond ((consp term)
	 (source-variables-in (cdr term)
			      (source-variables-in (car term) sofar)))
	((or (typep term 'source-variable)
	     (typep term 'source-ro-variable))
	 (let ((name (send term ':name)))
	   (cond ((eq name ':unbound)
		  sofar)
		 ((memq (setq name (gethash name *symbol-table*)) sofar)
		  sofar)
		 (t (cons-in-area name sofar *prolog-work-area*)))))
	(t sofar)))


(defun prolog-top-level-prove-body (raw-predication)
  (let* ((predication (parse-term raw-predication))
	 (cells (source-variables-in raw-predication nil))
	 (def (current-definition ':top-level-predication nil)))
    (or
	(cond (def (funcall (definition-prover def) (continuation (true)) predication))
	      ((and (setq def (and (symbolp (car predication))
				   (current-definition (car predication))))
		    (definition-deterministic def))
	       (apply (definition-prover def)
		      (continuation (funcall 'top-level-continuation cells t))
		      (cdr predication)))
	      (t (prove-conjunction (prolog-list predication)
				    (continuation (funcall 'top-level-continuation cells)))))
	(untrail *mark*)
	(format t "~%No (more) solutions."))))

TV:
(DEFUN KBD-INTERCEPT-prolog-BREAK (CHAR &REST IGNORE)
  "Perform the action normally associated with the Break character.
This function is intended to be called from IO-BUFFER output functions."
  (SETQ INHIBIT-SCHEDULING-FLAG NIL)		;It was T in the IO-BUFFER-OUTPUT-FUNCTION
  prolog:
  (unwind-protect
      (progn
	(push *mark* *mark-stack*)
	(setq *mark* (fill-pointer *trail-array*))
	(si:prolog-break))
    (setq *mark* (pop *mark-stack*)))    
  (VALUES CHAR T))


SI:
(DEFUN prolog-break ()
  "Read-prove-print loop for use as subroutine.
Many variables are rebound, as specified in SI::*BREAK-BINDINGS*."
  (let ((OLD-STANDARD-INPUT *STANDARD-INPUT*)
	(OLD-QUERY-IO *QUERY-IO*))

    (declare (unspecial old-query-io old-standard-input);so we can compile this file correctly in 104
	     (ignore old-query-io))		;so luser can find it in stack frame
    (PROGW *BREAK-BINDINGS*
      ;; Deal with keyboard multiplexing in a way similar to the error-handler.
      ;; If we break in the scheduler, set CURRENT-PROCESS to NIL.
      ;; If this is not the scheduler process, make sure it has a run reason
      ;; in case we broke in the middle of code manipulating process data.
      ;; If INHIBIT-SCHEDULING-FLAG is set, turn it off and print a warning.
      (WHEN (AND (BOUNDP 'SCHEDULER-STACK-GROUP)
		 (EQ %CURRENT-STACK-GROUP SCHEDULER-STACK-GROUP))
	(SETQ CURRENT-PROCESS NIL))
      (AND (NOT (NULL CURRENT-PROCESS))
	   (NULL (SEND CURRENT-PROCESS :RUN-REASONS))
	   (SEND CURRENT-PROCESS :RUN-REASON 'BREAK))
      (WHEN INHIBIT-SCHEDULING-FLAG
	(FORMAT T "~%---> Turning off INHIBIT-SCHEDULING-FLAG, you may lose. <---~%")
	(SETQ INHIBIT-SCHEDULING-FLAG NIL))
      (MULTIPLE-VALUE-BIND (SAVED-BUFFER SAVED-BUFFER-POSITION)
	  (SEND-IF-HANDLES OLD-STANDARD-INPUT :SAVE-RUBOUT-HANDLER-BUFFER)
	(FORMAT T "~&;Prolog Breakpoint, ~:@C to continue, ~:@C to quit.~%" #\RESUME #\ABORT)
	(LET* ((LAST-TIME-READTABLE NIL)
	       VALUE)
	  (DO-FOREVER
	    (CHECK-FOR-READTABLE-CHANGE LAST-TIME-READTABLE)
	    (SETQ LAST-TIME-READTABLE *READTABLE*)
	    (TERPRI)
	   LOOK-FOR-SPECIAL-KEYS
	    (LET ((CHAR (SEND *STANDARD-INPUT* :TYI)))
	      ;; Intercept characters even if otherwise disabled in program broken out of.
	      (COND ((AND (BOUNDP 'TV::KBD-STANDARD-INTERCEPTED-CHARACTERS)
			  (ASSQ CHAR TV::KBD-STANDARD-INTERCEPTED-CHARACTERS))
		     (FUNCALL (CADR (ASSQ CHAR TV:KBD-STANDARD-INTERCEPTED-CHARACTERS))
			      CHAR))
		    ((= CHAR (CHAR-INT #\RESUME))
		     (SEND *STANDARD-OUTPUT* :STRING-OUT "[Resume]")
		     (TERPRI)
		     (RETURN NIL))
		    (T (SEND *STANDARD-INPUT* :UNTYI CHAR))))
	    ;; Hide earlier dynamuc resume handlers
	    (LET ((EH::CONDITION-RESUME-HANDLERS (CONS T EH::CONDITION-RESUME-HANDLERS))
		  (THROW-FLAG T))
	      (CATCH-ERROR-RESTART ((SYS:ABORT DBG:DEBUGGER-CONDITION) "Return to top level in ~A."
				    (OR (SEND-IF-HANDLES SI:*TERMINAL-IO* :NAME) "current process."))
		(TERPRI)
		(MULTIPLE-VALUE-BIND (TEM1 TEM)
		    (WITH-INPUT-EDITING (*STANDARD-INPUT* '((:FULL-RUBOUT :FULL-RUBOUT)
							    (:ACTIVATION CHAR= #\END)))
		      (READ-FOR-TOP-LEVEL))
		  (IF (EQ TEM ':FULL-RUBOUT)
		      (GO LOOK-FOR-SPECIAL-KEYS))
		  (setq - TEM1))
		(LET ((prolog:PROLOG-TOP-LEVEL-INSIDE-EVAL T))
		  (prolog:prolog-top-level-prove -))
		(SETQ THROW-FLAG NIL))
	      (WHEN THROW-FLAG
		(FORMAT T "~&;Back to Prolog Breakpoint,  ~:@C to continue, ~:@C to quit.~%" #\RESUME #\ABORT))))
	      
	      ;; Before returning, restore and redisplay rubout handler's buffer so user
	  ;; gets what he sees, if we broke out of reading through the rubout handler.
	  ;; If we weren't inside there, the rubout handler buffer is now empty because
	  ;; we read from it, so leave it alone.  (Used to :CLEAR-INPUT).
	  (WHEN SAVED-BUFFER
	    (SEND OLD-STANDARD-INPUT :RESTORE-RUBOUT-HANDLER-BUFFER
		  SAVED-BUFFER SAVED-BUFFER-POSITION))
	  VALUE)))))

(compile-flavor-methods prolog-query undefined-predicate-error)

