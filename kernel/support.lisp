;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;This file contains more macros and utility functions for LM-Prolog


(defvar *structure-area*
	(make-static-area ':name 'structure-area ':region-size #o400000)
  "an area for all permanent (or semi-permanent) consing in Prolog")

(defsubst assq-2 (x y)
  ;;this is to avoid a spurious error from Symbolics' microcoded ASSQ
  #-symbolics (assq x y)
  #+symbolics (ass 'eq x y))

(defsubst memq-2 (x y)
  ;;this is to avoid a spurious error from Symbolics' microcoded MEMQ
  #-symbolics (memq x y)
  #+symbolics (mem 'eq x y))

;STRING-EQUAL got a surprisingly high ranking when I metered DEFINE.
(defmacro string-equal-symbol (string symbol &optional prefix-p)
  `(%string-equal ,string 0 (get-pname ,symbol) 0
		  ,(cond ((and prefix-p (stringp string))
			  (array-active-length string))
			 (prefix-p `(array-active-length ,string)))))

(defstruct (definition (:type list)
                       (:constructor nil)
                       :conc-name)
  prover            ;;function of the continuation and the predication's arguments
  interpreter-slot  ;;see below
  indexer           ;;function for adding new clauses 
  predicator        ;;name of predicate defined
  options           ;;options given to define merged with *default-options*
  indexes)          ;;hash tables for indexes of predicate

(defstruct (interpreter-slot (:type list)
                             (:constructor nil)
                             :conc-name)
  deterministic     ;;non-nil if the predicate is deterministic
  prover            ;;either the prover or NIL if the interpreter can handle it
  clauses)           ;;the clauses making up the definition

(defsubst definition-clauses (definition)
  (interpreter-slot-clauses (definition-interpreter-slot definition)))

(defsubst definition-deterministic (definition)
  (interpreter-slot-deterministic (definition-interpreter-slot definition)))

(defsubst qc-file-in-progress ()
  #-symbolics compiler:undo-declarations-flag
  #+symbolics compiler:compiling-whole-file-p)

(defun create-definition (prover deterministic indexer predicator options
                          clauses interpret-p &optional indexes)
  (let-if (qc-file-in-progress) ((*structure-area* default-cons-area))
    (list-in-area *structure-area*
                  prover
                  (list-in-area *structure-area*
                                deterministic
                                (and (not interpret-p) prover)
                                clauses)
                  indexer predicator options indexes)))

(defsubst fast-car-location (list)
  ;;this is essentially car-location
  (%make-pointer dtp-locative list))

(defsubst bound-p (value) (not (value-cell-p value)))

(defsubst bound-cell-p (cell) (not (value-cell-p (contents cell))))

(define-dtp-table lisp-form-1 (x mode)
  ':initial-value #'prog1)

(define-dtp-table copy-term-1 (x)
  ':initial-value #+3600 #'prog1 #-3600 #'list*)

;;supporting lazy and eager collections, constraints, read-only variables etc.

;Base flavor for all flavors whose instances should be unifiable etc. Essential
;messages are
;;; :CAR(), :CDR()
;;; :LISP-FORM(copy/query/invoke/dont-invoke)
;;; :COPY() by default is SELF (ok if there are no unbound variables inside)
;;; :VARIABLE-P() by default is NIL (ok if it can't be an unbound variable)
;;; :QUERY-USER() by default asks what to do, returns yes, no, or proceed
;;; :UNIFY(term) by default unifies term with (send self ':ordinary-term)

;;the following must be defined for each kind of prolog-flavor
;;; :ORDINARY-TERM()  ;;return an ordinary LM-Prolog term (i.e. an s-expression)
;;can also return a prolog-flavor (e.g. itself even) but then must return T
;;as a second value.  This is the default.

(defun unbound-variable-p (x)
  (or (value-cell-p x)
      (and (typep x 'prolog-flavor)
           (send x ':variable-p))))


;;WHEN LEXICAL CLOSURES REALLY WORK, INSTALL THE FOLLOWING:
#+lexical
(defmacro continuation (body)
  (cond ((eq 'invoke (careful-first body)) (second body))
	((and (consp body) (null (cdr body))) `#',(car body))
	(t `#'(lambda () ,body))))

;;This once used Lisp Machine closures but the variables need not be special and
;;there are no side-effects performed upon them
;;instead of (funcall delayed-value) I use invoke (i.e. apply <first> <rest>)
#-lexical
(defmacro continuation (body)
  (cond ((atom body) `(continuation (prog1 ,body)))
        ((eq 'invoke (car body)) (cadr body))
        ((and (memq (car body) '(send funcall))
              (or (atom (cadr body))
                  (neq 'entrypoint-in-world (caadr body))))
         `(PROLOG-LIST ,@(cdr body)))
        ((and (eq 'lexpr-funcall (car body))
              (or (atom (cadr body))
                  (neq 'entrypoint-in-world (caadr body))))
         `(PROLOG-LIST* ,@(CDR BODY)))
        ((null (cdr body)) `',body)
        ((and (atom (car body)) (atom (cadr body)) (null (cddr body)))
         `(PROLOG-LIST #',(car body) ,(cadr body)))
        (t (let ((variables (union () (continuation-variables body))))
             `(PROLOG-LIST #'(lambda ,variables ,body) ,@variables)))))

(deffun continuation-variables (body &optional is-a-cdr sofar)
  (cond ((symbolp body)
         (cond ((get body ':compiled-local-variable) (cons body sofar))
               (t sofar)))
        ((consp body)
         (cond (is-a-cdr
                (continuation-variables (car body) nil
                 (continuation-variables (cdr body) t sofar)))
               ((eq 'quote (car body)) sofar)
               ((memq (car body) '(let let*))
		(nconc
		  (nset-difference
		    (continuation-variables (cdr body) t ())
		    (mapcar #'careful-first (cadr body)))
		  sofar))
               ((memq (car body) '(with-stack-list with-stack-list*))
		(nconc
		  (delq (caadr body) (continuation-variables (cdr body) t ()))
		  sofar))
               (t (continuation-variables (car body) nil
                   (continuation-variables (cdr body) t sofar)))))
        (t sofar)))

#-lexical
(defmacro remind (who operation &rest args)
  `(trail (continuation (send ,who ,operation . ,args))))

#+lexical
(defmacro remind (who operation &rest args)
  (let ((bindings (mapcar #'(lambda (value) (list (gensym) value)) args)))
    `(let ((who ,who) . ,bindings)
       (trail (continuation (send who ,operation . ,(mapcar 'car bindings)))))))


#-lexical
(defmacro remind-call (what &rest args)
  `(trail (continuation (funcall ,what . ,args))))

#+lexical
(defmacro remind-call (what &rest args)
  (let ((bindings (mapcar #'(lambda (value) (list (gensym) value)) args)))
    `(let ,bindings
       (trail (continuation (funcall ,what . ,(mapcar 'car bindings)))))))

;;Source terms in compiled code aren't in *structure-area*
(defsubst structure-area-p (area)
  (memq area '#,(list *structure-area*
		      #-CommonLisp si:fasl-constants-area
		      #+CommonLisp si:macro-compiled-program)))

#+symbolics
(defsubst temporary-area-p (area)
  (plusp (si:%logldb si:%%region-temporary (si:area-region-bits area))))

#-symbolics
(defsubst temporary-area-p (area)
 (si:area-temporary-p area))

;;These three were written to reduce wasteful consing when tracing and printing...
(defun prolog-string (control-string &rest args)
  (let-if *prolog-work-area* ((default-cons-area *prolog-work-area*))
    (lexpr-funcall #'format nil control-string args)))

(defun prolog-symbol (control-string &rest args)
  (let-if *prolog-work-area* ((default-cons-area *prolog-work-area*))
    (make-symbol
      (lexpr-funcall #'format nil control-string args))))

(defun permanent-symbol (control-string &rest args)
  (make-symbol (lexpr-funcall #'format nil control-string args) t))

(defun prolog-intern (control-string &rest args)
  (intern (lexpr-funcall #'prolog-string control-string args)))

(defun prolog-db-symbol (predicator world category)
  (let ((package (pkg-find-package "PROLOG")))
    (prolog-intern "~S-IN-~S-~A" predicator world category)))

(defsubst create-permanent-symbol (name)
  (create-symbol-1 name #'permanent-symbol))

(defsubst create-symbol (name)
  (create-symbol-1 name #'prolog-symbol))

(defsubst generate-interned-symbol (name)
  (create-symbol-1 name #'careful-intern))

(defun careful-intern (control-string &rest args)
  (multiple-value-bind (symbol old-p)
      (lexpr-funcall #'prolog-intern control-string args)
    (cond (old-p (generate-interned-symbol symbol))
          (t symbol))))

(deffun create-symbol-1 (name symbol-maker)
  ;;a much friendlier version of gensym
  (cond ((symbolp name)
         (let ((position-of-underbar (string-search-char #\_ (string name))))
           (cond ((null position-of-underbar)
                  (funcall symbol-maker
			   "~a_~d"
			   ;;make a string <name>_<generation-number>
			   name
			   (putprop name
				    (1+ (or (get name 'generation-number) 0))
				    'generation-number)))
                 (t (create-symbol-1 (substring name 0 position-of-underbar)
				     symbol-maker)))))
        ((consp name) (create-symbol-1 (first name) symbol-maker))
        ((numberp name)
	 (create-symbol-1 (prolog-intern "NUMBER_~d" name) symbol-maker))
        ((stringp name) (create-symbol-1 (prolog-intern name) symbol-maker))
        (t (prolog-ferror ':bad-symbol "Can't make a symbol out of ~s" name))))

;;a world is represented by a symbol
;;on its property list (under prolog-predicates)
;;are the predicates defined in that world
;;The primary use of worlds is to select among various definitions of the same
;;predicate indexed by worlds

(defsubst predicators (world) (get world 'prolog-predicators))

;;be careful about areas here since it goes into A-memory
(setq *universe* (list-in-area sys:permanent-storage-area ':user ':system))

(deffun universe-ok (worlds)
  (cond ((null worlds))
	((and (consp worlds)
	      (symbolp (first worlds))
	      ;;Why, Ken?
	      ;;(neq (%p-data-type worlds) dtp-external-value-cell-pointer)
	      (not (temporary-area-p (%area-number worlds))))
	 (universe-ok (rest1 worlds)))
	(t ;;(prolog-error ':bad-universe "bad ~S" worlds)
	 nil)))

(deffun set-universe (worlds)
  ;;this is a seperate function so that it can be advised
;;  (cond ((universe-ok worlds)
	 (setq *universe* worlds))
;;	(t (print `(bad ,worlds))
;;         (setq *universe* (copylist worlds default-cons-area)))))

(defsubst definitions (predicator)
  (get predicator 'prolog-definitions))

;;the prolog-definitions are a list of the form:
;;((<universe-of-last-current-definition> . <last-current-definition>)
;; (<world-1> . <definition-in-world-1>)
;; ...
;; (<world-n> . <definition-in-world-n>))

(defsubst definition-in-world (predicator world)
  (REST1 (assq world (definitions predicator))))

#+(and (not symbolics) CommonLisp)
(defsetf definition-in-world (predicator world) (definition)
  `(put-definition-in-world ,definition ,predicator ,world))

#-(and (not symbolics) CommonLisp)
(defprop definition-in-world
         ((definition-in-world predicator world)
          put-definition-in-world
          si:val predicator world)
         setf)

(defsubst last-definition-universe (definitions)
  (first (first definitions)))

(defsubst last-definition (definitions)
  (REST1 (first definitions)))

(deffun put-definition-in-world (definition predicator world)
  (cond ((null definition) ;;really removing the definition
         (setf (definitions predicator)
               (delq (assq world (definitions predicator))
                     (definitions predicator))))
        (t (let ((definitions (definitions predicator)))
             (cond ((null definitions)
                    (setf (definitions predicator)
                          (list-in-area *structure-area*
                                        (list*-in-area *structure-area* nil nil)
                                        (list*-in-area *structure-area*
						       world
						       definition))))
                    (t (let ((old-pair (assq world definitions)))
                         (cond ((null old-pair)
                                (setf (definitions predicator)
                                      (list*-in-area *structure-area*
                                                     (first definitions)
                                                     (list*-in-area *structure-area*
								    world
								    definition)
                                                     (rest1 definitions))))
                               (t (setf (REST1 old-pair) definition))))
                       ;;flush current definition cache
                       (setf (last-definition-universe definitions) nil)))))))

(deffsubst memq-difference (x list end-list)
  (cond ((eq x (first list)) list)
        ((neq list end-list)
         (memq-difference x (rest1 list) end-list))))

(deffsubst find-first-definition (definitions worlds
                                              &optional worlds-checked best-so-far)
  (cond ((null definitions) best-so-far)
        (t (let ((new-worlds-checked
                   (memq-difference (first (first definitions))
                                    worlds
                                    worlds-checked)))
             (cond ((eq new-worlds-checked worlds) ;;i.e. in the first world
                    (REST1 (first definitions)))
                   ((null new-worlds-checked) ;;inactive definition
                    (find-first-definition (rest1 definitions)
                                           worlds worlds-checked best-so-far))
                   (t (find-first-definition (rest1 definitions)
                                             worlds new-worlds-checked
                                             (REST1 (first definitions)))))))))

(defmacro predication-definition (predication &optional (worlds '*universe*))
  `(let ((definitions (predication-definitions ,predication)))
     (cond ((eq (last-definition-universe definitions) ,worlds)
            (last-definition definitions))
           (t (find-and-cache-first-definition definitions ,worlds)))))

(defmacro sharp-comma (x)
  (cond ((qc-file-in-progress)
         `'(,compiler:eval-at-load-time-marker . ,x))
        (t `',(eval x))))

;;In normal predicate-to-predicate calls in compiled code, the predicator is known, and
;;we use optimizations in CURRENT-ENTRYPOINT. The interpreter and runtime sys
;;use this.
(defmacro current-definition
	  (predicator-form &optional (error-p t) (worlds '*universe*))
  `(cond ((symbolp ,predicator-form)
	  (let ((definitions (definitions ,predicator-form)))
	    (cond ((eq (last-definition-universe definitions) ,worlds)
		   (last-definition definitions))
		  ((find-and-cache-first-definition
		     definitions ,worlds ,(and error-p predicator-form))))))
	 (t ,(cond (error-p
		    `(current-definition-error ,predicator-form ,worlds))))))

(deffun current-definition-error (predicator worlds)
  (let ((new (prolog-error ':predicator-not-symbolic
			   "the predicator ~S should be a symbol"
			   predicator)))
    (current-definition new t worlds)))

(defstruct (index (:type list)
                  :conc-name
                  (:constructor nil))
 key-finder table)

(defsubst create-index (key-finder table)
  (list-in-area *structure-area* key-finder table))

(defprop prolog-error t :error-reporter)

(defun prolog-error (signal-name &rest signal-name-arguments)
  (lexpr-funcall #'cerror t nil signal-name signal-name-arguments))

(defprop prolog-ferror t :error-reporter)

(defun prolog-ferror (signal-name &rest signal-name-arguments)
  (lexpr-funcall #'cerror nil nil signal-name signal-name-arguments))

(defvar *circularity-mode* ':handle) ;;Can be either ':ignore, ':handle or ':prevent

(defvar *undefined-predicate-mode* ':signal) ;;Can be ':signal or ':fail

(defvar *variable-template*)
(defvar *template-index*)

#-PROLOG-MICRO-CODE
(PROGN 'COMPILE

(DEFUN make-cons (first rest) (list*-in-area *structure-area* 3 first rest))

(DEFUN make-constant (x) (cons-in-area 0 x *structure-area*))

(DEFUN MAKE-FIRST-OCCURRENCE (READ-ONLY)
  (let ((index (1- (incf *template-index*))))
    (list*-in-area *structure-area* (cond (read-only 4) (t 1)) index)))

(DEFUN MAKE-NON-FIRST-OCCURRENCE (TEMPLATE READ-ONLY)
  (list*-in-area *structure-area* (COND (READ-ONLY 5) (T 2)) (rest1 template)))

(DEFUN MAKE-VOID (read-only)
  (list*-in-area *structure-area* (cond (read-only 6) (t 7))))

(DEFUN first-occurrence-p (term) (MEMQ (first term) '(1 4)))

(DEFUN MAKE-VOID-OCCURRENCE (VARIABLE)
  (cond (CDR (ASSQ (CAR VARIABLE) '((1 . 7) (4 . 6)))) (CDDR VARIABLE)))

)

#+PROLOG-MICRO-CODE #8R
(PROGN 'COMPILE

(DEFUN MAKE-CONS (FIRST REST) (CONS-IN-AREA FIRST REST *STRUCTURE-AREA*))

(DEFUN MAKE-CONSTANT (X) (AND X (%MAKE-POINTER DTP-LOCATIVE (LIST-IN-AREA *STRUCTURE-AREA* X))))

(defsubst MAKE-OCCURRENCE (CLASS INDEX)
  (SI:%LOGDPB CLASS 2503 INDEX))

(DEFUN MAKE-FIRST-OCCURRENCE (READ-ONLY)
  (let ((index (1- (incf *template-index*))))
    (MAKE-OCCURRENCE (cond (read-only 4) (t 0)) INDEX)))

(DEFUN MAKE-NON-FIRST-OCCURRENCE (TEMPLATE READ-ONLY)
  (MAKE-OCCURRENCE (COND (READ-ONLY 5) (T 1)) TEMPLATE))

(DEFUN MAKE-VOID (read-only)
  (MAKE-OCCURRENCE (cond (read-only 6) (t 2)) 0))

(DEFUN FIRST-OCCURRENCE-P (TEMPLATE)
  (ZEROP (SI:%LOGLDB 2502 TEMPLATE)))

(DEFUN MAKE-VOID-OCCURRENCE (TEMPLATE)
  (SI:%LOGDPB 2 2502 (SI:%LOGDPB 0 0023 TEMPLATE)))

)

(defvar *contains-cut*)

(defun clause-template (predications)
  (let* ((*variable-template* ())
         (*template-index* 0)
         (*contains-cut* nil)
         (template
           (cons-in-area (make-interpreter-template (rest1 (first predications)))
                         (make-interpreter-template (rest1 predications))
                         *structure-area*)))
    (values
      (void-if-unique *variable-template* (first predications) template)
      *contains-cut*)))


(defun ensure-prolog-syntax ()
  (cond ((neq 'source-variable-read-macro (get-macro-character #/? *readtable*))
	 (format t "~%Warning: *READTABLE* has not been customized for Prolog' ~
~%Type (PROLOG:INSTALL-VARIABLE-SYNTAX) to do so.")
	 (break "PROLOG"))))

(defun make-interpreter-template (term)
  (ensure-prolog-syntax)
  (multiple-value-bind (template-or-constant template-p)
      (term-template-1 term)
    (cond (template-p template-or-constant)
	  (t (make-constant template-or-constant)))))

;Returns TERM,NIL or TEMPLATE,T
(defun term-template-1 (term)
  (cond ((consp term)
         (multiple-value-bind (first template-first-p)
	     (term-template-1 (first term))
	   (multiple-value-bind (rest template-rest-p)
	       (term-template-1 (rest1 term))
	     (cond ((or template-first-p template-rest-p)
		    (values
		      (make-cons
			(cond (template-first-p first)
			      (t (make-constant first)))
			(cond (template-rest-p rest)
			      (t (make-constant rest))))
		      t))
		   (t (cond ((equal '(cut) term) (setq *contains-cut* t)))
		      (values (select (%area-number term)
				(*structure-area* term)
				(otherwise (cons-in-area first rest *structure-area*)))
			      nil))))))
	((value-cell-p term)
	 (values
	   (make-instance-in-area *prolog-work-area* 'lisp-locative ':cell term)
	   nil))
	((typep term 'source-variable)
	 (values
	   (source-variable-template (send term ':name) nil)
	   t))
	((typep term 'source-ro-variable)
	 (values
	   (source-variable-template (send term ':name) t)
	   t))
	((typep term 'prolog-flavor)
	 (multiple-value-bind (ordinary-term prolog-flavor-p)
	     (send term ':ordinary-term)
	   (cond (prolog-flavor-p
		  (values ordinary-term nil))
		 (t (term-template-1 ordinary-term)))))
	(t (values term nil))))

(defun source-variable-template (name read-only)
  (cond ((eq name ':unbound) (make-void read-only))
	(t
	 (let ((old-variable-template (assq name *variable-template*)))
	   (cond ((null old-variable-template)
		  (let ((template (make-first-occurrence read-only)))
		    (push-in-area (prolog-list name template) *variable-template* *prolog-work-area*)
		    template))
		 ((first-occurrence-p (second old-variable-template))
		  (let ((template
			  (make-non-first-occurrence (second old-variable-template) read-only)))
		    (setf (second old-variable-template) template)
		    template))
		 (t (make-non-first-occurrence (second old-variable-template) read-only)))))))


(defvar *warn-if-variable-occurs-once* t)

#-symbolics
(deff prolog-warn 'compiler:warn)

#+symbolics
(defun prolog-warn (ignore ignore control-string &rest arguments)
  ;;compiler:warn incompatibly changed on Symbolics
  (terpri)
  (lexpr-funcall #'format t control-string arguments))

(defun subst-in-area (area new old term)
  (let ((default-cons-area area))
    (subst new old term)))

(deffun void-if-unique (variable-template-pairs head template)
 (cond ((not (null variable-template-pairs))
	(let ((template (first variable-template-pairs)))
	  (cond ((first-occurrence-p (second template))
		 (and *warn-if-variable-occurs-once*
		      (or (string-equal-symbol "IGNORE" (first template) t)
			  (prolog-warn ':variable-occurs-once
				       ':implausible
				       "~%Warning: ?~a occurs just once in (~a ...)."
				       (first template)
				       head)))
		 (void-if-unique (cdr variable-template-pairs)
				 head
				 (subst-in-area *structure-area*
						(make-void-occurrence (second template))
						(second template)
						template)))
		(t (void-if-unique (cdr variable-template-pairs) head template)))))
       (t template)))

(defvar *variables-alist* () "Alist used when copying terms to preserve isomorphy")

;;*vector* is long enough for 4 recursive entries to %unify-term-with-template
;;or %construct, beyond that the more expensive resources are used.
;;the need for a new *vector* is when unifying constraints or clauses
;;inside of the interpreter

(defresource vector ()
  :constructor (make-list 256. ':area *structure-area*))

(defvar *original-vector* (make-list 256. ':area *structure-area*))
(setq *vector* *original-vector*)

(defmacro with-new-*vector* (&body body)
 `(let ((*vector* (rest1 (%make-pointer-offset dtp-list *vector* 63.))))
    (cond ((null *vector*)
	   (using-resource (*vector* vector)
	     ,@body))
	  (t ,@body))))

(defsubst plain-displace (old new)
  (setf (first old) (first new))
  (setf (rest1 old) (rest1 new)))

(defmacro push-if-not-memq (item access)
  `(let ((item ,item))
     (cond ((not (memq item ,access)) (push item ,access)))))

(defmacro push-if-not-member (item access)
  `(let ((item ,item))
     (cond ((not (member item ,access)) (push item ,access)))))

(defconst *circularity-marker* (cons nil nil))
(defconst *circularity-cons* (cons *circularity-marker* *circularity-marker*))

;;Can't tail recurse due to WITH-CONS-BOUND-TO-CONS.
(defun circular-p (x)
  (cond ((consp x)
	 (cond ((structure-area-p (%area-number x)) nil)
	       (t
		(WITH-CONS-PARTS X
		  (let ((first (first x))
			(rest1 (rest1 x)))
		    (cond ((or (eq first *circularity-marker*)
			       (eq rest1 *circularity-marker*)))
			  (t (WITH-CONS-BOUND-TO-CONS x *circularity-cons*
			       (or (circular-p first) (circular-p rest1))))))))))
        ((typep x 'prolog-flavor)
         (multiple-value-bind (ordinary-term prolog-flavor-p)
             (send x ':ordinary-term)
           (and (not prolog-flavor-p) (circular-p ordinary-term))))))

(define-dtp-entry copy-term-1 dtp-locative (x)
  (let ((assq (assq-2 x *variables-alist*)))
    (cond (assq (cdr assq))
          (t (let ((c (%cell0)))
	       (push-in-area (prolog-cons x c) *variables-alist* *prolog-work-area*)
	       c)))))

(define-dtp-entry copy-term-1 dtp-list (ignore)
  (prolog-ferror ':no-circularity-mode
		 "No circularity mode seems to have been selected!"))

;;This is what we want to say. Unfortunately, DTP-RPACD-FORWARD trick doesn't work here.
;;(defun copy-cons-circular (x)
;;  (with-cons-parts x
;;    (cond ((or (eq (car x) 'to-be-clobbered) (eq (cdr x) 'to-be-clobbered))
;;	     x)
;;	  (t (let ((car-x (car x))
;;		   (cdr-x (cdr x))
;;		   (temporary
;;		     (cons-in-area
;;		       'to-be-clobbered 'to-be-clobbered *prolog-work-area*)))
;;	       (with-cons-bound-to-cons x temporary
;;		 (rplaca temporary (%reference (copy-term-1 car-x)))
;;		 (rplacd temporary (%reference (copy-term-1 cdr-x)))
;;		 temporary))))))

(defun copy-cons-circular (x)
  (cond ((structure-area-p (%area-number x)) x)
	(t (let ((item (assq-2 x *conses-alist*))) ;;the slow but simple way...
	     (cond (item (cdr item))
		   (t (with-stack-list*
			(pair x (cons-in-area 'to-be-clobbered 'to-be-clobbered
					      *prolog-work-area*))
			(with-stack-list* (*conses-alist* pair *conses-alist*)
			  (rplaca (cdr pair) (%reference (copy-term-1 (car x))))
			  (rplacd (cdr pair) (%reference (copy-term-1 (cdr x))))
			  (cdr pair)))))))))

(defun copy-cons-no-circular (x)
  (cond ((structure-area-p (%area-number x)) x)
	(t (prolog-cons (copy-term-1 (car x)) (copy-term-1 (cdr x))))))

(define-dtp-entry copy-term-1 dtp-instance (x)
  (cond ((typep x 'prolog-flavor) (send x ':copy)) (t x)))

(defun copy-term (term)
  (let ((*variables-alist* ())) (copy-term-1 term)))

(deffun keyify (value)
  (select (%data-type value)
    (dtp-list (keyify (car value)))
    (dtp-instance
     (cond ((typep value 'prolog-flavor)
            (multiple-value-bind (ordinary-term prolog-flavor-p)
                (send value ':ordinary-term)
              (cond (prolog-flavor-p ordinary-term)
                    (t (keyify ordinary-term)))))
           (t value)))
    (t value)))

(deffun index-selector-form (arglist form)
  (cond ((and (symbolp arglist) (string-equal-symbol "+" arglist t)) form)
        ((CONSP arglist)
         (or (index-selector-form (car arglist) `(careful-first ,form))
             (index-selector-form (cdr arglist) `(careful-rest1 ,form))))))

(deffun do-to-each-index (indexes argument-list action)
  (cond (indexes
         (let* ((index (first indexes))
                (table (index-table index))
                (key (funcall (index-key-finder index) argument-list)))
           (cond ((not (value-cell-p key))
                  (funcall action key table (gethash key table))))
           (do-to-each-index (rest1 indexes) argument-list action)))))


(defun make-instance-in-area (area flavor &rest init-plist)
  (instantiate-flavor flavor (locf init-plist) nil nil area))

(defun make-instance-in-area-and-initialize (area flavor &rest init-plist)
  (instantiate-flavor flavor (locf init-plist) t nil area))

;Default methods for PROLOG-FLAVOR.

(defmethod (prolog-flavor :car) ()
  (multiple-value-bind (ordinary-term prolog-flavor-p)
      (send self ':ordinary-term)
    (cond (prolog-flavor-p
           (prolog-error ':cant-take-car "Can't take CAR of ~s" ordinary-term))
          (t (car ordinary-term)))))

(defmethod (prolog-flavor :cdr) ()
  (multiple-value-bind (ordinary-term prolog-flavor-p)
      (send self ':ordinary-term)
    (cond (prolog-flavor-p
           (prolog-error ':cant-take-cdr "Can't take CDR of ~s" ordinary-term))
          (t (cdr ordinary-term)))))

(defmethod (prolog-flavor :copy) () self)

(defmethod (prolog-flavor :unify) (other)
  (multiple-value-bind (ordinary-term prolog-flavor-p)
      (send self ':ordinary-term)
    (and (not prolog-flavor-p) ;;what about EQ?
         (%unify-term-with-term ordinary-term other))))

(defmethod (prolog-flavor :lisp-form) (mode)
  (selectq mode
    (:copy
     (multiple-value-bind (ordinary-term prolog-flavor-p)
         (send self ':ordinary-term)
       (cond (prolog-flavor-p
	      (prolog-ferror 'lisp-form-copy "~s was encountered during lisp-form :copy"
			    ordinary-term))
             (t (lisp-form-1 ordinary-term mode)))))
    (:invoke
     (multiple-value-bind (ordinary-term prolog-flavor-p)
         (send self ':ordinary-term)
       (cond (prolog-flavor-p ordinary-term)
             (t (lisp-form-1 ordinary-term mode)))))
    (:dont-invoke self)
    (:query 
     (selectq (send self ':query-user)
       (no self)
       (yes
        (multiple-value-bind (ordinary-term prolog-flavor-p)
            (send self ':ordinary-term)
          (cond (prolog-flavor-p ordinary-term)
                (t (lisp-form-1 ordinary-term mode)))))
       (proceed
        (multiple-value-bind (ordinary-term prolog-flavor-p)
            (send self ':ordinary-term)
          (cond (prolog-flavor-p ordinary-term)
                (t (lisp-form-1 ordinary-term ':invoke)))))))
    (otherwise
     (send self ':lisp-form
	   (prolog-error 'bad-lisp-form-mode
			 "~s is not a recoginized lisp-form mode" mode)))))

;;Defaults.
(defmethod (prolog-flavor :query-user) () 'yes) ;;good default???

(defmethod (prolog-flavor :variable-p) () nil) ;;good default

(defmethod (prolog-flavor :ordinary-term) ()
  (values self t))


(defmethod (source-variable :unify) (x)
  (unify x (%dereference cell)))

(defmethod (source-variable :reconstruction-init-plist) ()
  (list ':name name))

;This broke Manny's def-word.
;(defmethod (source-variable 
;  (cond ((variable-boundp cell) cell)
;	(t (setq cell (%cell name)))))

(defmethod (source-variable :ensure-cell) ()
  (setq cell (%cell0)))

(defmethod (source-variable :print-self) (stream ignore ignore)
  (send stream ':tyo #/?)
  (cond ((neq name ':unbound) (prin1 name stream))))

(defmethod (source-variable :print-binding) ()
  (and (neq name ':unbound)
       (variable-boundp cell)
       (neq cell (%dereference cell))
       (format t "~%?~S = ~S"
	       name
	       (lisp-form (%dereference cell) ':query))))

(defmethod (source-ro-variable :unify) (x)
  (let ((value (%dereference cell)))
    (cond ((not (value-cell-p value))
           (unify value x)))))

(defmethod (source-ro-variable :reconstruction-init-plist) ()
  (list ':name name))

;This broke Manny's def-word
;(defmethod (source-ro-variable :ensure-cell) ()
;  (cond ((variable-boundp cell) cell)
;	(t (setq cell (%cell name)))))

(defmethod (source-ro-variable :ensure-cell) ()
  (setq cell (%cell0)))

(defmethod (source-ro-variable :print-self) (stream ignore ignore)
  (send stream ':string-out "??")
  (cond ((neq name ':unbound) (prin1 name stream))))

(defmethod (source-ro-variable :print-binding) ()
  (and (neq name ':unbound)
       (variable-boundp cell)
       (neq cell (%dereference cell))
       (format t "~%?~S = ~S"
	       name
	       (lisp-form (%dereference cell) ':query))))

(defmethod (lisp-locative :ordinary-term) ()
  cell)

(defmethod (lisp-locative :lisp-form) (ignore)
  cell)

(defmethod (lisp-locative :unify) (other)
  (and (typep other 'prolog-flavor)
       (eq cell (send other ':ordinary-term))))


(defvar *symbol-table* :unbound "Hash table to handle variable names in user I/O.")

(defun parse-term (term &optional ignore)  ;was global-p
  (ensure-prolog-syntax)
  (parse-term-1 term))

(defun parse-term-1 (term)
  (cond ((consp term)
         (prolog-cons
           (parse-term-1 (car term))
           (parse-term-1 (cdr term))))
	((value-cell-p term)
	 (make-instance-in-area *prolog-work-area* 'lisp-locative ':cell term))
	((typep term 'source-variable)
	 (parse-source-variable term))
	((typep term 'source-ro-variable)
	 (make-instance-in-area
	   *prolog-work-area* 'read-only-variable
	   ':cell (parse-source-variable term)))
	((typep term 'prolog-flavor)
	 (multiple-value-bind (ordinary-term prolog-flavor-p)
	     (send term ':ordinary-term)
	   (cond (prolog-flavor-p ordinary-term)
		 (t (parse-term-1 ordinary-term)))))
	(t term)))

(defun parse-source-variable (term)
  (let (aux
	(name (send term ':name)))
    (cond ((eq name ':unbound) (%cell0))
	  ((setq aux (gethash name *symbol-table*))
	   (%dereference (send aux ':cell)))	;It may have become bound,
						;e.g. in a "global read".
	  ((setq aux (send term ':ensure-cell))
	   (remind-call 'delete-symbol term)
	   (insert-symbol term)
	   aux))))


(define-dtp-entry lisp-form-1 dtp-locative (x mode)	;Release 3
  (cond ((eq mode ':copy)
	 (prolog-ferror 'lisp-form-copy "A variable was encountered during lisp-form :copy")))
  (let ((form (gethash x *symbol-table*)))
    (cond (form
	   (cond ((typep form 'source-variable) form)
		 (t (make-instance-in-area *prolog-work-area*
					       'source-variable
					       ':cell x
					       ':name (send form ':name)))))
	  ((setq form (make-instance-in-area *prolog-work-area*
					     'source-variable
					     ':cell x
					     ':name (unique-name)))
	     (remind-call 'delete-symbol form)
	     (insert-symbol form)))))

(defun delete-symbol (source-variable)
  (remhash (send source-variable ':cell) *symbol-table*)
  (remhash (send source-variable ':name) *symbol-table*)
  nil)

(defun insert-symbol (source-variable)
  (puthash (send source-variable ':cell) source-variable *symbol-table*)
  (puthash (send source-variable ':name) source-variable *symbol-table*)
  source-variable)

(defun unique-name ()
  (let ((index (// (send *symbol-table* ':filled-entries) 2))
	(char-buffer (make-array 10 ':type 'art-string ':fill-pointer t)))
    (setf (fill-pointer char-buffer) 0)
    (array-push char-buffer (+ #/A (\ index 26.)))
    (do ((i (// index 26) (// i 10.)))
	((= i 0))
      (array-push char-buffer (+ #/0 (\ i 10.))))
    (do ((name (intern char-buffer) (intern char-buffer)))
	((not (gethash name *symbol-table*))
	 name)
      (array-push char-buffer #/X))))



(define-dtp-entry lisp-form-1 dtp-list (ignore ignore)
  (prolog-ferror ':no-circularity-mode
		 "No circularity mode seems to have been selected!"))

;;This is what we want to say. Unfortunately, DTP-RPLACD-FORWARD trick doesn't work here.
;;(defun cons-form-circular (x)
;;  (with-cons-parts x
;;    (cond ((or (eq (car x) 'to-be-clobbered) (eq (cdr x) 'to-be-clobbered))
;;	     x)
;;	  (t (let ((car-x (car x))
;;		   (cdr-x (cdr x))
;;		   (temporary
;;		     (cons-in-area
;;		       'to-be-clobbered 'to-be-clobbered *prolog-work-area*)))
;;	       (with-cons-bound-to-cons x temporary
;;		 (rplaca temporary (%reference (lisp-form-1 car-x)))
;;		 (rplacd temporary (%reference (lisp-form-1 cdr-x)))
;;		 temporary))))))

(defun cons-form-circular (x mode)
;  (cond ((structure-area-p (%area-number x)) x)
;	(t
	 (let ((item (assq-2 x *conses-alist*))) ;;the slow but simple way...
	   (cond (item (cdr item))
		 (t (with-stack-list*
		      (pair x (cons-in-area 'to-be-clobbered 'to-be-clobbered
					    *prolog-work-area*))
		      (with-stack-list* (*conses-alist* pair *conses-alist*)
			(rplaca (cdr pair) (%reference (lisp-form-1 (car x) mode)))
			(rplacd (cdr pair) (%reference (lisp-form-1 (cdr x) mode)))
			(cdr pair))))))
;	 ))
  )

(defun cons-form-no-circular (x mode)
  (prolog-cons (lisp-form-1 (first x) mode) (lisp-form-1 (rest1 x) mode))
;This is too clever...
;  (cond ((structure-area-p (%area-number x)) x)
;	((eq mode ':copy)
;	 (prolog-cons (lisp-form-1 (first x) mode) (lisp-form-1 (rest1 x) mode)))
;	(t
;	 (let ((new-first (lisp-form-1 (first x) mode))
;	       (new-rest (lisp-form-1 (rest1 x) mode)))
;	   (cond ((and (eq new-first (first x)) (eq new-rest (rest1 x))) x)
;		 (t (prolog-cons new-first new-rest))))))
  )

(define-dtp-entry lisp-form-1 dtp-instance (x mode)
  (cond  ((typep x 'prolog-flavor) (send x ':lisp-form mode))
	 (t x)))

(defun lisp-form (x mode)
  ;;Called by run-time system, not by compiled code.
 (selectq mode
   (:COPY (LET ((*PROLOG-WORK-AREA* WORKING-STORAGE-AREA)) (LISP-FORM-1 X MODE)))
   (otherwise (lisp-form-1 x mode))))

(defmacro establish-condition-handlers (&body body)
  `(condition-bind (
;		    ((si:undefined-function)
;		     #'(lambda (condition)
;			 (cond ((definitions (send condition ':function-name))
;				(going-to-prolog-p (send condition ':function-name))))))
		    #-symbolics
		    ((eh:stack-frame-too-large)
                     #'(lambda (ignore)
                         (prolog-ferror ':unbound-variable-as-rest-argument
"The Prolog compiler does not support calls
whose last cons ends with a unbound variable.")))
                    ((si:unclaimed-message)
                     #'(lambda (condition)
                         (let ((message
				 (send condition #-symbolics ':get ':message)))
                           (cond ((eq message ':unify)
                                  ;;should change arguments too!!
                                  (values ':new-operation ':send-if-handles))))))
                    ((si:wrong-type-argument eh:arg-type-error)
                     #'(lambda (condition)
			 (let (argument)
			   (cond ((setq argument (send condition ':send-if-handles ':arg-pointer))
				  (cond ((typep argument 'prolog-flavor)
					 (values ':argument-value (send argument ':ordinary-term)))))
				 ((setq argument (send condition ':send-if-handles ':old-value))
				  (cond ((typep argument 'prolog-flavor)
					 (values ':substitute-new-value-in-stack-call (send argument ':ordinary-term))))))))))
		   ,@body))

;;used in control-primitives and by instead-of-ucode
(deffun variables-in-no-circularity (term &optional so-far)
  (cond ((consp term)
         (variables-in-no-circularity
	  (rest1 term)
	  (variables-in-no-circularity (first term) so-far)))
        ((unbound-variable-p term)
         (cond ((memq-2 term so-far) so-far)
               (t (prolog-cons term so-far))))
        (t so-far)))

(defun variables-in-circularity (term &optional so-far)
  (cond ((consp term)
         (with-cons-parts term
           (let ((first (first term))
                 (rest1 (rest1 term)))
             (cond ((eq first *circularity-marker*) so-far)
                   (t (with-cons-bound-to-cons term *circularity-cons*
                        (variables-in-circularity first
                             (variables-in-circularity rest1 so-far))))))))
        ((unbound-variable-p term)
         (cond ((memq-2 term so-far) so-far)
               (t (prolog-cons term so-far))))
        (t so-far)))

(deffun not-ground-p-no-circularity (x)		;7.12
  (cond ((consp x)
         (or (not-ground-p-no-circularity (car x))
	     (not-ground-p-no-circularity (cdr x))))
         ((unbound-variable-p x) x)))

(defun not-ground-p-circularity (x)		;7.12
  (cond ((consp x)
         (with-cons-parts x
           (let ((first (first x))
                 (rest1 (rest1 x)))
             (cond ((eq first *circularity-marker*) nil)
                   (t (with-cons-bound-to-cons x *circularity-cons*
                        (or (not-ground-p-circularity first)
			    (not-ground-p-circularity rest1))))))))
        ((unbound-variable-p x) x)))

;;This returns either T or NIL,some-x,some-y where some-x,some-y is a counter-example.
(defun identical-p (x y)
  (let ((mark *trail*))
    (cond ((eq x y) t)
	  ((not (unify x y)) (untrail mark) (values nil t nil))
	  ((= mark *trail*) t)
	  ((value-cell-p (aref *trail-array* mark))
	   (let* ((item1 (aref *trail-array* mark))
		  (item2 (cdr item1)))
	     (untrail mark)
	     (values nil (%dereference item1) (%dereference item2))))
	  ((value-cell-p (aref *trail-array* (1+ mark)))
	   (let* ((item1 (aref *trail-array* (1+ mark)))
		  (item2 (cdr item1)))
	     (untrail mark)
	     (values nil (%dereference item1) (%dereference item2))))
	  (t (prolog-ferror ':internal "IDENTICAL can't find values to return.")))))

(defun set-circularity-mode (mode-name)
  (selectq mode-name
    (:ignore (install-circularity-mode-ignore)
             (alter-dtp-entry lisp-form-1 dtp-list #'cons-form-no-circular)
             (alter-dtp-entry copy-term-1 dtp-list #'copy-cons-no-circular)
             (setf #'variables-in 'variables-in-no-circularity)
             (setf #'not-ground-p 'not-ground-p-no-circularity)
             (setq *circularity-mode* mode-name))
    (:handle (install-circularity-mode-handle)
             (alter-dtp-entry lisp-form-1 dtp-list #'cons-form-circular)
             (alter-dtp-entry copy-term-1 dtp-list #'copy-cons-circular)
             (setf #'variables-in 'variables-in-circularity)
             (setf #'not-ground-p 'not-ground-p-circularity)
             (setq *circularity-mode* mode-name))
    (:prevent (install-circularity-mode-prevent)
              (alter-dtp-entry lisp-form-1 dtp-list #'cons-form-no-circular)
              (alter-dtp-entry copy-term-1 dtp-list #'copy-cons-no-circular)
              (setf #'variables-in 'variables-in-no-circularity)
              (setf #'not-ground-p 'not-ground-p-no-circularity)
              (setq *circularity-mode* mode-name))
    (otherwise
     (set-circularity-mode
       (prolog-error ':bad-circularity-mode
                     "~s should be either :IGNORE, :HANDLE, or :PREVENT" mode-name)))))

(set-circularity-mode ':ignore) ;;for speed

(defun set-undefined-predicate-mode (mode-name)
  (selectq mode-name
    ((:signal :fail)
     (setq *undefined-predicate-mode* mode-name))
    (otherwise
     (set-undefined-predicate-mode
       (prolog-error ':bad-undefined-predicate-mode
                     "~s should be either :SIGNAL or :FAIL" mode-name)))))

#+3600
(advise compiler:phase-1-warning :around let-if-spurious-warning 0
  (cond ((not (string-equal
                (first arglist) 
                "VALUE-CELL-LOCATION on local or instance variable ~S; ~
use LOCF or VARIABLE-LOCATION"))
         :do-it)))

(defmacro with-who-line (string &body body)
  `(let ((old-who-state (si:process-wait-whostate current-process)))
    (unwind-protect
      (progn (setf (si:process-wait-whostate current-process) ,string)
             (tv:who-line-run-state-update)
             ,@body)
      (setf (si:process-wait-whostate current-process) old-who-state)
      (tv:who-line-run-state-update))))

;(compile-encapsulations 'si:print-truly-random-object)

;;This logically belongs to DB-SUPPORT, but is used there inside another macroexpansion.
(defmacro option-value (type-form options
                        &optional (default-options '*default-options*))
  (cond ((and (consp type-form) (eq (first type-form) 'quote))
         (let* ((type (second type-form))
                (selector (get type 'value-option-selector)))
           (cond ((null selector)
                  (prolog-ferror ':undefined-define-option
				 "~s is not a define-predicate option" type))
                 (t `(,selector
                      (or (assq-2 ,type-form (rest1 ,options))
                          (assq-2 ,type-form (rest1 ,default-options))))))))
        (t `(funcall (or (get ,type-form 'value-option-selector)
                         (prolog-ferror ':undefined-define-option
					"~s is not a define-predicate option" ,type-form))
                     (or (assq-2 ,type-form (rest1 ,options))
                         (assq-2 ,type-form (rest1 ,default-options)))))))

(defmacro advise-within-each (list-within-functions &rest arguments)
  `(progn ,@(mapcar #'(lambda (within-function)
                        `(advise-within ,within-function ,@arguments))
                    list-within-functions)))

(defmacro unadvise-within-each (list-within-functions &rest arguments)
  `(progn ,@(mapcar #'(lambda (within-function)
                        `(unadvise-within ,within-function ,@arguments))
                    list-within-functions)))


;;; For lambda-expressions...

(defun resolve-lambda-clause (cont &rest arglist)
  (declare (special *instance*))
  (send *instance* ':resolve-cont cont (rest-arg-copy arglist)))

(defmethod (lambda-clause :resolve-cont) (cont arglist)
  (with-new-*vector*
    (and (%unify-term-with-template arglist (car templates))
	 (prove-conjunction-if-need-be (%construct (cdr templates)) cont))))

(defmethod (lambda-clause :print-self) (stream level escape)
  (cond ((variable-boundp *symbol-table*)
	 (let ((x (with-new-*vector* (%construct templates)))
	       (mark *trail*)
	       (*print-escape* escape)
	       (*print-level* (and *print-level* (- *print-level* level)))
	       (*print-pretty* nil)			;otherwise, bad loop!
	       )
	   (unwind-protect
	       (progn
		 (send stream ':string-out "#<")
		 (dolist (goal x)
		   (send stream ':string-out " ")
		   (write (lisp-form-1 goal ':dont-invoke) ':stream stream))
		 (send stream ':string-out ">"))
	     (untrail mark))))
	(t
	 (using-resource (*symbol-table* symbol-table)
	   (using-resource (tr trail 500)
	     (with-trail tr
	       (send self :print-self stream level escape)))))))


(defun make-lambda-template (globals lambda-list goals)
  (let ((*variable-template* ())
	(*template-index* 0)
	(*warn-if-variable-occurs-once* nil)
	(*structure-area* *prolog-work-area*))
      (let ((templates
	      (cons-in-area (make-lambda-template-1 globals lambda-list)
			    (make-lambda-template-1 globals goals)
			    *structure-area*)))
	(make-instance-in-area *prolog-work-area* 'lambda-clause ':templates
			       (void-if-unique *variable-template* lambda-list templates)))))


(defun make-lambda-template-1 (globals term)
  (multiple-value-bind (template-or-constant template-p)
      (lambda-template-1 globals term)
    (cond (template-p template-or-constant)
	  (t (make-constant template-or-constant)))))


;Returns TERM,NIL or TEMPLATE,T
(defun lambda-template-1 (globals term)
  (cond ((memq-2 term globals)
	 (values term nil))
	((value-cell-p term)
	 (values
	   (lambda-variable-template term)
	   t))
	((consp term)
         (multiple-value-bind (first template-first-p)
	     (lambda-template-1 globals (first term))
	   (multiple-value-bind (rest template-rest-p)
	       (lambda-template-1 globals (rest1 term))
	     (cond ((or template-first-p template-rest-p)
		    (values
		      (make-cons
			(cond (template-first-p first)
			      (t (make-constant first)))
			(cond (template-rest-p rest)
			      (t (make-constant rest))))
		      t))
		   (t (values (prolog-cons first rest) nil))))))
	((typep term 'prolog-flavor)
	 (multiple-value-bind (ordinary-term prolog-flavor-p)
	     (send term ':ordinary-term)
	   (cond (prolog-flavor-p
		  (values ordinary-term nil))
		 (t (lambda-template-1 globals ordinary-term)))))
	(t (values term nil))))

(defun lambda-variable-template (name)
  (let ((old-variable-template (assq-2 name *variable-template*)))
    (cond ((null old-variable-template)
	   (let ((template (make-first-occurrence nil)))
	     (push-in-area (prolog-list name template) *variable-template* *prolog-work-area*)
	     template))
	  ((first-occurrence-p (second old-variable-template))
	   (let ((template
		   (make-non-first-occurrence (second old-variable-template) nil)))
	     (setf (second old-variable-template) template)
	     template))
	  (t (make-non-first-occurrence (second old-variable-template) nil)))))



(compile-flavor-methods
  prolog-flavor source-variable source-ro-variable lisp-locative lambda-clause)
