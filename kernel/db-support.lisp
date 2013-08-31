;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;This defines the multiple worlds where predicates live in LM-Prolog

(defmacro define-predicate (predicator &body options+clauses)
  ;;options are a list of options beginning with the symbol "options"
  ;;if nothing is there same as if the option list were (options)
  (cond ((null options+clauses)
         (make-definition predicator nil nil))
        ((eq (first (first options+clauses)) ':options)
         (make-definition predicator (first options+clauses)
                          (rest1 options+clauses)))
        (t (make-definition predicator nil options+clauses))))

(defvar *predicator-being-defined*)

(defvar *file-default-options* ()
  "The options default for a specific file. May contain :MULTIPLE.")

(defvar *eval-when*)

(defvar *default-options*
        '(options (:type :static)
		  (:world :user)
;;never used      (:if-unique-variable :warn)
		  (:if-another-definition :ignore)
;;obsolete	  (:execution :interpreted)
		  (:place-clauses :anywhere)
		  (:if-old-definition :flush)
		  (:compile-method :closed)
;;obsolete	  (:save-compiled-code nil)
		  (:lisp-macro-name nil)
		  (:deterministic :sometimes)
		  (:argument-list (&rest :|No argument list provided|))
		  (:documentation "is not documented."))
  "This is the default options for DEFINE-PREDICATE.  All options must be defaulted here.")

(eval-when (compile load eval)
(defprop :type second value-option-selector)

(defprop :world second value-option-selector)

(defprop :indexing-patterns rest1 value-option-selector)

;;(defprop :if-unique-variable second value-option-selector)

;;currently can be either :flush or :keep
;; :query and :error to come
(defprop :if-old-definition second value-option-selector)

(defprop :if-another-definition second value-option-selector)

;;(defprop :execution second value-option-selector)

(defprop :deterministic second value-option-selector)

(defprop :place-clauses second value-option-selector)

(defprop :compile-method rest1 value-option-selector)

(defprop :documentation second value-option-selector)

;;(defprop :save-compiled-code second value-option-selector) ;;for old time's sake

(defprop :argument-list second value-option-selector)

(defprop :lisp-macro-name second value-option-selector)

(defprop :for-partial-prolog second value-option-selector)
)

(defun merge-options (options defaults)
  (cons ':options (merge-options-1 (rest1 options) (rest1 defaults))))

(defun merge-options-1 (options-body defaults-body)
  (append options-body (alist-difference defaults-body options-body)))

(deffun alist-difference (options exceptions)
  (cond ((not (null options))
         (cond ((and (neq (first (first options)) ':multiple)
		     (assq (first (first options)) exceptions))
                (alist-difference (rest1 options) exceptions))
               (t (cons (first options)
                        (alist-difference (rest1 options) exceptions)))))))

(defun disjunctive-normal-form (options)
  (let ((all (disjunctive-normal-form-1
	       (merge-options options *file-default-options*)))
	unique)
    (mapc #'(lambda (x) (push-if-not-member x unique)) all)
    (nreverse unique)))

;;We want a list ((option option ...) (option option ...) ...).
(defun disjunctive-normal-form-1 (spec)
  (cond (spec
	 (selectq (car spec)
	   (:options
	    (apply #'cartesian (mapcar #'disjunctive-normal-form-1 (cdr spec))))
	   (:multiple (mapcan #'disjunctive-normal-form-1 (cdr spec)))
	   (t (ncons (ncons spec)))))
	(t (ncons spec)) ;;the spec () is taken as an empty conjunction
	))

(defun cartesian (&rest disjunctions)
  (let (*conses-alist*) (cartesian-1 () disjunctions) (nreverse *conses-alist*)))

(defun cartesian-1 (item disjunctions)
  (cond ((null disjunctions) (push item *conses-alist*))
	(t (mapc #'(lambda (x) (cartesian-1 (merge-options-1 item x) (cdr disjunctions)))
		 (car disjunctions)))))

(defvar *definition* nil "The current definition, both for new and revised ones.")

(deffun find-and-cache-first-definition
        (definitions worlds &optional predicator-or-no-error)
  (let ((current-definition (find-first-definition (rest1 definitions) worlds)))
    (cond ((and (not *step*) (not (null current-definition)))
           (setf (last-definition-universe definitions) worlds)
           (setf (last-definition definitions) current-definition)
           current-definition)
	  ((not (null current-definition))
	   (let ((world (option-value ':world (definition-options current-definition))))
	     (cond ((eq world 'traced-predicates)
		    (find-and-cache-first-definition
		      definitions (cdr worlds) predicator-or-no-error))
		   (t ;;Return a definition of DO-STEP in :SYSTEM
		      ;;with its prover closing over the real definition.
		      ;;NB. The prover lives in two slots for interpreter's sake.
		    (let* ((d (definition-in-world 'do-step ':system))
			   (prover (let-closed ((*definition* current-definition)) (car d))))
			(prolog-list* prover
				      (prolog-list nil prover (definition-clauses d))
				      (cddr d)))))))
          (predicator-or-no-error
           (undefined-predicate predicator-or-no-error worlds)))))

(defun make-definition (predicator options lisp-clauses)
  (let ((*step* nil))
    `(progn 'compile
	    ,@(mapcan #'(lambda (x) (copylist	;Don't trust MAPCAN
				      (make-definition-1 predicator (cons ':options x) lisp-clauses)))
		      (disjunctive-normal-form options)))))

(defun forward-value-cell-safe (from to)
  (or (eq (follow-cell-forwarding (value-cell-location from) t)
	  (follow-cell-forwarding (value-cell-location to) t))
      (si:forward-value-cell from to)))

(forward-value-cell-safe 'compile-p
			 #-symbolics 'zwei:compile-p
			 #+symbolics 'compiler:compiler-warnings-context)

(defvar compile-p nil "This is T only if macro-expanding for the compiler.")

#+symbolics
(advise readfile :around lm-prolog 0
  (let (compile-p) :do-it))

#-Symbolics
(forward-value-cell-safe 'compile-processing-mode 'zwei:compile-processing-mode)

#-Symbolics
(defvar compile-processing-mode nil "This is T only if macro-expanding for the compiler.")

(defun make-definition-1 (predicator options lisp-clauses)
  (warn-if-unrecognized-option (rest1 options) predicator)
  #-Symbolics
  (cond ((and (eq compile-processing-mode 'compiler:micro-compile)
	      (not (option-value ':compile-method options ())))
	 (setq options (merge-options '(:options (:compile-method :micro-compiled)) options))))
  (let* (compilers-forms prover-form option-form
	 (indexing-patterns (option-value ':indexing-patterns options))
         (explicit-world (option-value ':world options ()))
         (world (option-value ':world options))
         (*eval-when*
           (cond ((qc-file-in-progress) '(compile load eval))
                 (t '(load eval))))
         (execution
	   (SELECTQ (CAR (OPTION-VALUE ':COMPILE-METHOD OPTIONS))
	     ((:INTRINSIC :MICRO-COMPILED) ':COMPILED)	;convenience
	     (T (COND ((OR (QC-FILE-IN-PROGRESS) COMPILE-P) ':COMPILED)
		      (T ':INTERPRETED)))))
         (*contains-cut* nil)
         (make-indexes-form ;;;this adds to the guy above
           (and indexing-patterns
		(make-indexes-form predicator world indexing-patterns)))
         #+symbolics (copy-of-clauses (cond ((qc-file-in-progress)
                                             (copytree lisp-clauses))
                                            (t lisp-clauses)))
	 ;;some strange bug in dumping out lisp-clauses (they've been clobbered)
	 )
    (let* ((clauses (make-clauses #-symbolics lisp-clauses
				  #+symbolics copy-of-clauses
				  predicator world))
	   )
      (selectq (option-value ':if-old-definition options)
        (:flush         
         (selectq execution
           (:interpreted
            (setq option-form
		  `',options
		  prover-form
		  (make-interpreter-definition predicator options indexing-patterns)))
           (:compiled
            (multiple-value (prover-form option-form compilers-forms)
              (make-compiler-definition predicator options clauses indexing-patterns)))
           (:never (setq prover-form ''predicate-declared-to-never-be-executed)))
         `((eval-when ,*eval-when*
	     (add-def-to-world
	       ,prover-form
	       ',predicator
	       ,option-form
	       ,(cond ((qc-file-in-progress)
		       `(let ((*contains-cut* ',*contains-cut*)
			      (*warn-if-variable-occurs-once* nil))
			  (make-clauses ',lisp-clauses ',predicator ',world)))
		      (t `',clauses))
	       ,(and (eq execution ':interpreted)
		     (not *contains-cut*)
		     (eq ':ignore (option-value ':if-another-definition options))
		     (null indexing-patterns))
	       ,(car make-indexes-form)))
	   ,@(cond (indexing-patterns `(,@(cdr make-indexes-form))))
	   ,@compilers-forms
	   ,@(let ((macro-name (option-value ':lisp-macro-name options)))
	       (cond ((not (null macro-name))
		      `((defmacro ,macro-name (&rest arguments)
			  (list 'query-once
				(list 'quote (cons ',predicator arguments))
				'':lisp-term nil))))))
	   ,(let ((functions
		    (union ()
			   (functions-defined-in-forms
			     `((progn 'compile ,@compilers-forms)
			       (progn 'compile ,@(cdr make-indexes-form)))
			     ()))))
	      `(update-the-prover ',predicator ',world ',functions))))
      (:keep
       (selectq execution
	 (:compiled
	  (multiple-value (prover-form option-form compilers-forms)
              (make-compiler-definition predicator options clauses indexing-patterns))))
       `((revise-definition ',predicator ',options ',lisp-clauses ',explicit-world)
	 ,@compilers-forms
	 ))
      (otherwise
       (prolog-ferror ':bad-define-option "~s should be either :KEEP or :FLUSH"
	       (option-value ':if-old-definition options)))))))


(defun compile-if-need-be (function-spec)
  (cond ((not (qc-file-in-progress))
         (let ((definition (AND (FBOUNDP FUNCTION-SPEC) (FSYMEVAL FUNCTION-SPEC))))
           (cond ((consp definition) (with-who-line "Compile" (compile function-spec))))))))

(deffun functions-defined-in-forms (forms sofar)
  (cond ((null forms) sofar)
	((memq (first (first forms)) '(defun deffun deffsubst))
	 (functions-defined-in-forms (cdr forms) (cons (cadar forms) sofar)))
	((or (EQ (CAAR FORMS) 'LOCAL-DECLARE)
	     (and (eq (caar forms) 'progn) (equal (cadar forms) ''compile)))
	 (FUNCTIONS-DEFINED-IN-FORMS (CDR FORMS)
				     (FUNCTIONS-DEFINED-IN-FORMS (CDDAR FORMS) sofar)))
	(t (functions-defined-in-forms (cdr forms) sofar))))

(defun make-interpreter-definition (IGNORE options indexing-patterns)
  (let ((default-name
	  (intern (STRING-APPEND
		    "PROVER"
		    (cond (indexing-patterns "-INDEXED") (t ""))
		    (cond ((eq (option-value ':deterministic options) ':always) "-DET")
			  (t ""))
		    (cond ((or *contains-cut*
			       (eq (option-value ':type options) ':dynamic))
			   "-DYNAMIC")
			  (t ""))
		    "-IGNORE")
		  "PROLOG")))
    `(let-closed (*current-clauses* ,@(cond (indexing-patterns `(*current-indexes*))))
       #',default-name)))

(defvar *current-clauses*)

(defvar *current-indexes*)

(eval-when (compile eval)
(defvar *options-det* '(:options (:deterministic :always)))

(defmacro define-provers (if-another-definition)
  (let (*contains-cut*
	(*default-options* `(:options (:if-another-definition ,if-another-definition))))
    `(progn 'compile
	    ,(interpreter-prover-defun
	       (prolog-intern "PROVER~A-~A" "" if-another-definition)
	       '*current-clauses* nil nil nil nil)
	    ,(interpreter-prover-defun
	       (prolog-intern "PROVER~A-~A" '-indexed if-another-definition)
	       '*current-clauses* '*current-indexes* nil nil nil)
	    ,(interpreter-prover-defun
	       (prolog-intern "PROVER~A-~A" '-det if-another-definition)
	       '*current-clauses* nil *options-det* nil nil)
	    ,(interpreter-prover-defun
	       (prolog-intern "PROVER~A-~A" '-indexed-det if-another-definition)
	       '*current-clauses* '*current-indexes* *options-det* nil nil)
	    ,@(prog1 nil (setq *contains-cut* t))
	    ,(interpreter-prover-defun
	       (prolog-intern "PROVER~A-~A" '-dynamic if-another-definition)
	       '*current-clauses* nil nil nil nil)
	    ,(interpreter-prover-defun
	       (prolog-intern "PROVER~A-~A" '-indexed-dynamic if-another-definition)
	       '*current-clauses* '*current-indexes* nil nil nil)
	    ,(interpreter-prover-defun
	       (prolog-intern "PROVER~A-~A" '-det-dynamic if-another-definition)
	       '*current-clauses* nil *options-det* nil nil)
	    ,(interpreter-prover-defun
	       (prolog-intern "PROVER~A-~A" '-indexed-det-dynamic if-another-definition)
	       '*current-clauses* '*current-indexes* *options-det* nil nil)
	    )))

(defun interpreter-prover-defun (prover-name clauses-name indexes-name options IGNORE IGNORE)
  `(defun ,prover-name (continuation &rest arguments)
     ,(cond (*unsafe-rest-argument* `(setq arguments (rest-arg-copy arguments)))
	    (t `(cond ((consp arguments) (rest-arg-fixup-loop arguments)))))
     ,(let* ((DETERMINACY (eq (option-value ':deterministic options) ':always))
	     (BODY-1 `(cond ((contents ,clauses-name)
			     (,@(cond (indexes-name `(try-indexed ,indexes-name))
				      (t `(try-each)))
			       (contents ,clauses-name)
			       ,(COND (DETERMINACY '(CONTINUATION (TRUE)))
				      (T 'CONTINUATION))
			       arguments
			       *trail*))))
	     (BODY-2
	       (COND ((or *contains-cut*
			  (eq (option-value ':type options) ':dynamic))
		      `(LET ((*CUT-TAG* CONTINUATION)) ;;anything unique
			 (*CATCH *CUT-TAG* ,BODY-1)))
		     (T BODY-1))))
	(cond (DETERMINACY `(COND (,BODY-2 (INVOKE CONTINUATION))))
	      ((or *contains-cut* (eq (option-value ':type options) ':dynamic))
	       #-LEXICAL
	       `(let-if
		  (not (memq (first continuation) '(true false invoke-continuation)))
		  ((continuation
		     (CONTINUATION
		       (FUNCALL 'INVOKE-CONTINUATION CONTINUATION *CUT-TAG*))))
		  ,BODY-2)
	       #+lexical
	       `(LET* ((TEMP-TAG *CUT-TAG*)
		       (CONTINUATION
			 (CONTINUATION
			   (INVOKE-CONTINUATION CONTINUATION TEMP-TAG))))
		  ,body-2))
	      (t BODY-2)))))

)

(DEFINE-PROVERS :ignore)

;;(define-provers :try-before) LOSES.
;;(define-provers :try-after) LOSES.

;;A prover for a :IF-ANOTHER-DEFINITION :TRY-BEFORE is a closure of this,
;;closing over *C-DEFINITION* and *C-PROVER*.
(defun try-another-definition-before (&rest arguments)
  (declare (special *c-prover* *C-DEFINITION*))
  (let* ((another-definition
	   (another-definition
	     (definition-predicator *C-DEFINITION*)
	     (option-value ':world (definition-options *C-DEFINITION*))
	     *universe* ()))
	 (mark *trail*))
    (cond ((and another-definition
		(apply (definition-prover another-definition) arguments)))
	  ((untrail mark))
	  ((apply *c-prover* arguments)))))

;;A prover for a :IF-ANOTHER-DEFINITION :TRY-AFTER is a closure of this,
;;closing over *C-DEFINITION* and *C-PROVER*.
(defun try-another-definition-after (&rest arguments)
  (declare (special *c-prover* *C-DEFINITION*))
  (let* ((another-definition
	   (another-definition
	     (definition-predicator *C-DEFINITION*)
	     (option-value ':world (definition-options *C-DEFINITION*))
	     *universe* ()))
	 (mark *trail*))
    (cond ((apply *c-prover* arguments))
	  ((untrail mark))
	  ((and another-definition
		(apply (definition-prover another-definition) arguments))))))

;;This finds a definition ``after'' the one in WORLD, or NIL of there is none.
(deffun another-definition (predicator world universe seen-before)
  (cond ((null universe) nil)
	((null world)
	 (cond ((memq (first universe) seen-before)
		(another-definition predicator nil (rest1 universe) seen-before))
	       ((definition-in-world predicator (first universe)))
	       (t
		(another-definition predicator nil (rest1 universe) seen-before))))
	((eq world (first universe))
	 (another-definition predicator nil
			     (rest1 universe)
			     (prolog-cons world seen-before)))
	(t
	 (another-definition predicator world
			     (rest1 universe)
			     (prolog-cons (first universe) seen-before)))))

(deffun make-indexes-form (predicator world indexing-patterns &optional defuns)
  (cond (indexing-patterns
	 (let* ((selector
		  `(keyify ,(index-selector-form (cdar indexing-patterns) 'x)))
		(defun
		  `(defun
		     ,(prolog-db-symbol predicator world
					(prolog-string "SELECTOR-~D"
						       (length defuns)))
		     (x) ,selector)))
	   (make-indexes-form
	     predicator world (cdr indexing-patterns) (cons defun defuns))))
	(t (let ((defuns (nreverse defuns)))
	     `((list-in-area *structure-area*
                 ,@(mapcar #'(lambda (defun)
                               `(create-index
				  ',(cadr defun)
                                  (make-hash-table ':area *structure-area*)))
                           defuns))
	       ,@defuns)))))

(defmacro add-clause-macro (clause access where &optional (clauses access))
  ;;are the callers of this careful about what area the consing happens?
  `(let ((clauses ,clauses))
     (selectq ,where
       ((:anywhere :before)
        (setf ,access (cons-in-area ,clause clauses *structure-area*)))
       (:after (setf ,access
		     (let ((default-cons-area *structure-area*))
		       (append clauses (list ,clause)))))
       (otherwise (prolog-ferror ':bad-place-clause-option
				 "~s should be either :anywhere, :before, or :after"
			  ,where)))))

(defmacro add-clause-gethash-macro (clause key table where clauses)
  ;;are the callers of this careful about what area the consing happens?
  `(let ((clauses ,clauses))
     (selectq ,where
       ((:anywhere :before)
        (puthash ,key (cons-in-area ,clause clauses *structure-area*) ,table))
       (:after (puthash ,key
			(let ((default-cons-area *structure-area*))
			  (append clauses (list ,clause)))
			,table))
       (otherwise (prolog-ferror ':bad-place-clause-option
				 "~s should be either :anywhere, :before, or :after"
			  ,where)))))

(deffun add-each-to-indexes (clauses indexes where)
  ;;this adds them in the reverse order of clauses
  (cond (clauses
         (add-each-to-indexes (rest1 clauses) indexes where)
	 (add-to-indexes (first clauses) indexes where))))

(defun add-to-indexes (clause indexes where)
  (with-new-*vector*
    (add-to-indexes-1 clause indexes where)))

(defun add-to-indexes-1 (clause indexes where)
  (declare (special clause where))
  (do-to-each-index indexes
                    (%construct (first (send clause ':templates)))
                    (closure '(clause where)
                             #'(lambda (key table value)
                                 (add-clause-gethash-macro
				   clause key table where value)))))

(defun define-predicate-1 (predicator options clauses)
  (let ((*step* nil))
    (let ((*warn-if-variable-occurs-once* nil))	;Lars-Henrik proposed this
      (mapc #'(lambda (x)
		(define-predicate-2 predicator (prolog-cons ':options x) clauses))
	    (disjunctive-normal-form (copytree options))))))

(defun define-predicate-2 (predicator options clauses)
  (cond ((eq (option-value ':if-old-definition options) ':keep)
	 (revise-definition predicator options clauses (option-value ':world options)))
        (t (mapc #'eval (make-definition-1 predicator options clauses)))))

(defun compile-definition (definition)
  (let ((compile-p t)
	(*warn-if-variable-occurs-once* nil)
	(*options* (definition-options definition))
	(*predicator-being-defined* (definition-predicator definition)))
    (selectq (option-value ':type *options*)
      (:static
       (let ((prover (selectq (option-value ':if-another-definition *options*)
		       (:ignore (definition-prover definition))
		       (t (closure-function (definition-prover definition))))))
	 (cond ((closurep prover)		;then it's interpreted
		(mapc #'eval (make-definition-1 *predicator-being-defined*
						*options*
						(definition-clauses definition)))))))
      (:dynamic
       (mapc #'(lambda (clause)
		 (let ((loc (locate-in-instance clause 'prover)))
		   (cond ((consp (cdr loc))	;then it's interpreted
			  (location-makunbound loc)
			  (unwind-protect
			    (with-who-line "Compile"
			      (compile `(:location ,loc) (compile-clause clause)))
			    (cond ((not (location-boundp loc))
				   (rplacd loc (send clause ':templates)))))))))
	     (definition-clauses definition))))))

(defun update-the-prover (predicator world &optional functions)
  (let ((*definition* (definition-in-world predicator world)))
    (cond ((definition-indexes *definition*)
	   (add-each-to-indexes (definition-clauses *definition*)
				(definition-indexes *definition*)
				(option-value ':place-clauses (definition-options *definition*)))))
    (mapc #'compile-if-need-be functions)
    (update-prover)))


;;This installs clauses and indexes in the closure of interpreted provers,
;;and installs :IF-ANOTHER-DEFINITION "encapsulation" if need be.
(defun update-prover ()
  (let ((closure (definition-prover *definition*))
	(clauses (locf (definition-clauses *definition*)))
	(indexes (definition-indexes *definition*)))
    (cond ((closurep closure)
	   (set-in-closure closure '*current-clauses* clauses)
	   (cond (indexes (set-in-closure closure '*current-indexes* indexes)))))
    (selectq (option-value ':if-another-definition (definition-options *definition*))
      (:try-before
       (let ((encapsulation (let-closed ((*c-prover* closure) (*c-definition* *definition*))
			      #'try-another-definition-before)))
	 (setf (definition-prover *definition*) encapsulation)
	 (setf (interpreter-slot-prover (definition-interpreter-slot *definition*))
	       encapsulation)))
      (:try-after
       (let ((encapsulation (let-closed ((*c-prover* closure) (*c-definition* *definition*))
			      #'try-another-definition-after)))
	 (setf (definition-prover *definition*) encapsulation)
	 (setf (interpreter-slot-prover (definition-interpreter-slot *definition*))
	       encapsulation)))))
  (definition-predicator *definition*))

(defun revise-definition (predicator options clauses world)
  (let* ((*contains-cut* nil)
	 (*warn-if-variable-occurs-once* nil)	;Warnings have already been issued.
	 (*definition*
	   (cond (world
		  (definition-in-world predicator world))
		 (t (current-definition predicator nil)))))
    (cond ((null *definition*)
           (mapc #'eval
		 (make-definition-1 predicator
				    (merge-options '(:options (:type :dynamic)
							      (:if-old-definition :flush))
						   options)
				    clauses)))
          (t (add-clauses clauses
                          *definition* 
                          (option-value ':place-clauses options
					(definition-options *definition*))
                          world)
             (cond (*contains-cut*
                    ;;this makes sure that the interpreter goes through the
                    ;;provers if a clause with a cut has been added
                    (setf (interpreter-slot-prover
                            (definition-interpreter-slot *definition*))
                          (definition-prover *definition*))))))))

(defun revise-clause (prover-spec clause/# out-of options predicator)
  "Installs (FDEFINITION PROVER-SPEC) as a clause's prover."
  (let* ((*definition*
	   (cond ((consp predicator) predicator)	;for compatibility
	   ((definition-in-world predicator (option-value ':world options)))
	   (t (current-definition predicator))))
	 (clauses (definition-clauses *definition*)))
    (compile-if-need-be prover-spec)
    ;;A crude way of avoiding FDEFINE warnings...
    (remprop prover-spec ':source-file-name)
    (send (cond ((symbolp clause/#) ;;actually the name of a named clause.
		 (first (mem #'(lambda (name clause) (eq name (send clause ':name)))
			     clause/# clauses)))
		(t ;;CLAUSE/#-th out of OUT-OF clauses
		 (nth (selectq
			(option-value ':place-clauses
				      options
				      (definition-options *definition*))
			(:after (+ clause/# (- out-of) (length clauses)))
			(otherwise clause/#))
		      clauses)))
	  ':set-prover
	  (fdefinition prover-spec))))

(defun remove-clause-named (name definition)
  (remove-clause
    (first
      (mem #'(lambda (name clause) (eq (send clause ':name) name))
           name
           (definition-clauses definition)))
    definition))

(defun remove-clause (clause definition)
  (with-new-*vector* (remove-clause-1 clause definition)))

(defun remove-clause-1 (clause definition)
  (declare (special clause)) ;;for the closure
  (cond (definition
         (setf (definition-clauses definition)
               (delq clause (definition-clauses definition) 1))
         (let ((indexes (definition-indexes definition)))
           (cond (indexes
                  (do-to-each-index
                    indexes
                    (%construct (first (send clause ':templates)))
                    (closure '(clause)
                             #'(lambda (key table value)
                                 (puthash key (delq clause value 1) table))))))))))

(defun remove-all-clauses (definition)
  (cond (definition
         (setf (definition-clauses definition) ())
         (mapc #'(lambda (index) (clrhash (index-table index)))
               (definition-indexes definition))
          t)))

(deffun add-clauses (clauses definition where world)
  (cond ((not (null clauses))
	 (cond ((neq where ':after)
		(add-clauses (rest1 clauses) definition where world)))
         (let ((clause
                 (make-clause (first clauses)
                              (definition-predicator definition)
                              world)))
           (or (replace-old-clause-of-same-name clause definition where)
               (funcall (definition-indexer definition)
                        clause definition where)))
	 (cond ((eq where ':after)
		(add-clauses (rest1 clauses) definition where world))))))

(defun replace-old-clause-of-same-name (new-clause definition where)
  (with-new-*vector*
    (replace-old-clause-of-same-name-1 new-clause definition where)))

(defun replace-old-clause-of-same-name-1 (new-clause definition where)
  (declare (special new-clause where)) ;;for the closures
  (let ((name (send new-clause ':name)))
    (cond ((symbolp name)    
           (let* ((clauses
                    (mem #'(lambda (name clause) (eq (send clause ':name) name))
                         name
                         (definition-clauses definition)))
                  (old-clause (first clauses)))
	     (declare (special old-clause))
             (cond (clauses
                    (setf (first clauses) new-clause)
                    (let ((indexes (definition-indexes definition)))
                      (cond (indexes
                             (do-to-each-index
                               indexes
                               (%construct (first (send old-clause ':templates)))
                               (closure '(new-clause old-clause)
                                        #'(lambda (ignore ignore value)
                                            (setf (first (memq old-clause value))
                                                  new-clause))))
                             (do-to-each-index
                               indexes
                               (%construct (first (send new-clause ':templates)))
                               (closure '(new-clause where)
                                        #'(lambda (key table value)
                                            (or (memq new-clause value)
                                                (add-clause-gethash-macro
                                                  new-clause key table where value))))))))
                    t)))))))

(deffun prolog-definition-of (predicator world)
  (let ((definition (definition-in-world predicator world)))
    (cond (definition 
           `(define-predicate ,(definition-predicator definition)
              ,(definition-options definition)
              ,@(definition-clauses definition))))))

(defun error-predicate-is-static (ignore definition ignore)
  (prolog-ferror ':assert-not-permitted "~s is not dynamic"
		 (definition-predicator definition)))

(defun error-predicate-is-primitive (ignore definition ignore)
  (prolog-ferror ':assert-not-permitted "~s is primitive"
		 (definition-predicator definition)))

(deffun make-clauses (lisp-clauses *predicator-being-defined* world)	;8.2
  (let-if (qc-file-in-progress) ((*structure-area* default-cons-area))
    (let* ((clauses (make-list (length lisp-clauses) ':area *structure-area*))
           (IGNORE
	     (make-clauses-1 lisp-clauses clauses *predicator-being-defined* world)))
      CLAUSES)))

(deffun make-clauses-1 (lisp-clauses clauses *predicator-being-defined* world)
 (cond ((null lisp-clauses) 'IGNORE)
       (t (LET ((CLAUSE
		  (make-clause
		    (first lisp-clauses) *predicator-being-defined* world)))
	    (setf (first clauses) clause)
            (make-clauses-1 (rest1 lisp-clauses) (rest1 clauses)
                            *predicator-being-defined* world)))))


(defmethod (clause :unify) (other)
  (cond ((symbolp name)
	 (cond ((and (consp other) (consp (rest1 other)) (consp (second other)))
		(with-new-*vector*
		  (and (unify name (first other))
		       (unify predicator (first (second other)))
		       (%unify-term-with-template (rest1 (second other))
						  (first templates))
		       (%unify-term-with-template (rest2 other)
						  (rest1 templates)))))
	       (t (unify other (send self ':ordinary-term)))))
	((and (consp other) (consp (first other)))
	 (with-new-*vector*
	   (and (unify predicator (first (first other)))
		(%unify-term-with-template (rest1 (first other))
					   (first templates))
		(%unify-term-with-template (rest1 other)
					   (rest1 templates)))))
	(t (unify other (send self ':ordinary-term)))))


(defmethod (clause :print-self) (stream level escape)
  (cond ((variable-boundp *symbol-table*)
	 (let ((x (send self ':ordinary-term))
	       (mark *trail*)
	       (*print-escape* escape)
	       (*print-level* (and *print-level* (- *print-level* level)))
	       (*print-pretty* nil)			;otherwise, bad loop!
	       )
	   (unwind-protect
	       (write (lisp-form-1 x ':dont-invoke) ':stream stream)
	     (untrail mark))))
	(t
	 (using-resource (*symbol-table* symbol-table)
	   (using-resource (tr trail 500)
	     (with-trail tr
	       (send self :print-self stream level escape)))))))

(defmethod (clause :ordinary-term) ()
  (let ((clause
	  (with-new-*vector*
	    (prolog-cons (prolog-cons predicator (%construct (first templates)))
			 (%construct (rest1 templates))))))
    (cond ((symbolp name) (prolog-cons name clause))
          (t clause))))

(defmethod (clause :query-user) () 'proceed) ;;don't ask user about converting this

(defmethod (clause :resolve) (continuation arguments)
  (funcall prover continuation arguments))

(defun make-clause (lisp-clause *predicator-being-defined* world)
  (cond ((and (typep lisp-clause 'clause) (eq world (send lisp-clause ':world)))
         LISP-CLAUSE)
        (t (multiple-value-bind (templates contains-cut name)
               (parse-clause lisp-clause)
             (setq *contains-cut* (or *contains-cut* contains-cut))
             (make-instance-in-area *structure-area*
	       'clause
	       ':PROVER TEMPLATES
	       ':templates templates
	       ':predicator *predicator-being-defined*
	       ':world world
	       ':contains-cut contains-cut
	       ':name (or name "No name"))))))

(defvar *options*)

(deffun parse-clause (lisp-clause)
  (cond ((atom lisp-clause)
         (cond ((typep lisp-clause 'clause)
                (send lisp-clause ':parse-clause))
               ((typep lisp-clause 'prolog-flavor)
                (multiple-value-bind (ordinary-term prolog-flavor-p)
                      (send lisp-clause ':ordinary-term)
                    (cond (prolog-flavor-p
			   (parse-clause-error ordinary-term))
                          (t (parse-clause ordinary-term)))))
               (t (parse-clause-error lisp-clause))))
        ((symbolp (first lisp-clause)) ;;it has a name
         (cond ((or (atom (rest1 lisp-clause)) (atom (second lisp-clause)))
		(parse-clause-error lisp-clause))
               ((neq *predicator-being-defined*
                     (first (first (rest1 lisp-clause))))
		(parse-clause-error-head lisp-clause))
               (t (multiple-value-bind (templates contains-cut)
                      (clause-template (rest1 lisp-clause))
                    (values templates contains-cut (first lisp-clause))))))
        ((neq *predicator-being-defined* (first (first lisp-clause)))
	 (parse-clause-error-head lisp-clause))
        (t (clause-template lisp-clause))))

(defun parse-clause-error (lisp-clause)
  (parse-clause
    (prolog-error ':bad-clause
		  "bad clause ~S must be a list of predications"
		  lisp-clause)))

(defun parse-clause-error-head (lisp-clause)
  (parse-clause
    (prolog-error ':bad-clause
		  "bad clause ~S the head of predicate ~s's clauses must begin with ~s"
		  lisp-clause *predicator-being-defined* *predicator-being-defined*)))

(defmethod (clause :parse-clause) ()
  (values templates contains-cut name))

(defun add-and-index-clause (clause definition where)
  (add-to-indexes clause (definition-indexes definition) where)
  (add-clause clause definition where))

(deffun add-clause (clause definition where)
  (add-clause-macro clause (definition-clauses definition) where))

(defvar *all-worlds* nil "All worlds ever created")

(defvar *protected-worlds* '(:system)
  "Masking of predicates in any of these worlds queries the user first.")

(defun add-def-to-world (prover predicator options clauses interpret-p indexes)
  (let* ((options (merge-options options *default-options*))
	 (deterministic (eq (option-value ':deterministic options ()) ':always))
	 (indexer (cond (indexes 'add-and-index-clause)
			(t (selectq (option-value ':type options ())
			     ((:dynamic) 'add-clause)
			     (otherwise 'error-predicate-is-static)))))
	 (*definition*
	   (create-definition prover deterministic indexer predicator options clauses interpret-p indexes)))
    (add-to-world predicator *definition*)))
			 

(defun add-to-world (predicator definition &optional world)
  (cond ((qc-file-in-progress)
	 (compiler:file-declare predicator 'prolog-definition definition))
	((let* ((world (or world (option-value ':world (definition-options definition))))
		(type
		  (cond ((get world 'define-predicate-type))
			(t ;;otherwise its a new world
			 (and (symbol-package world) (push world *all-worlds*))
			 ;;if the world is not interned this aught to be more clever
			 ;;so that stuff can be garbage collected...
			 (putprop world
				  (prolog-intern "DEFINE-PREDICATE-IN-~s" world)
				  'define-predicate-type)))))
	   (cond ((or inhibit-fdefine-warnings
		      (not-masking-protected-predicates predicator world))
		  (si:record-source-file-name predicator type)
		  (cond ((null (definition-in-world predicator world))
			 (setf (predicators world)
			       (cons predicator (predicators world)))))
		  (setf (definition-in-world predicator world) definition)
		  world))))))

(defun not-masking-protected-predicates (predicator world)
  (let ((definitions (definitions predicator)))
    (cond ((null definitions))
          (t (let ((universe-left (memq world *universe*)))
               (cond ((null universe-left))
                     (t (let ((masked-worlds
                                (intersection *protected-worlds*
                                              (rest1 universe-left))))
                          (cond ((null masked-worlds))
                                (t (let ((old-definition
                                           (find-first-definition definitions
                                                                  masked-worlds)))
                                     (cond ((null old-definition))
                                           (t (y-or-n-p
                                                (prolog-string
                                                        "~%You are about to mask the definition of ~s in ~s.~%Do you want to proceed? "
                                                        predicator
                                                        (option-value
                                                          ':world
                                                          (definition-options
                                                            old-definition)))))))))))))))))

(defun remove-from-world (predicator world)
  (setf (predicators world) (remove predicator (predicators world)))
  (setf (definition-in-world predicator world) nil)
  (setf (last-definition-universe (definitions predicator)) nil)) ;;flush cache

(defun predicate-documentation (predicator)
  (let ((definition (current-definition predicator nil)))
    (cond ((not (null definition))
           (values
             (option-value ':documentation (definition-options definition))
             t)))))

(defun predicate-argument-list (predicator)
  (let ((definition (current-definition predicator nil)))
    (cond ((not (null definition))
           (values
             (option-value ':argument-list (definition-options definition))
             t)))))

;;now for file attribute (-*- ... -*-) stuff

(defvar *add-world-when-loading* ':yes
  "If ':yes then the world of a file being loaded will be added to the current universe,
if ':ask then you will be asked,
otherwise it will not be added.")

;; A much simpler scheme in which :OPTIONS is the only file attribute.

(defprop :options t fs:known-file-attribute)

#+symbolics
(push ':options zwei:*attributes-remembered-in-buffer*)

(defun (:property :options fs:file-attribute-bindings) (ignore attribute value)
  (warn-if-unrecognized-option value nil)
  (let ((name (conjuncts-option-value ':world value)))
    (cond ((and name
		(not (memq name *universe*))
                (or (eq *add-world-when-loading* ':yes)
                    (and (eq *add-world-when-loading* ':ask)
                         (y-or-n-p
                           (prolog-string
                                   "~%The world ~s is not in the current universe, should I add it?"
                                   name)))))
           (set-universe (cons name *universe*))
           nil)))
  (values (list '*file-default-options*)
          `((,attribute
             ,@value
             ;;,@(alist-difference (rest1 *default-options*) value)
	     ))))

(deffun warn-if-unrecognized-option (options-left defining)
  (cond ((not (null options-left))
         (let ((option (first options-left)))
           (cond ((eq (first option) ':multiple)
		  (mapc #'(lambda (x) (warn-if-unrecognized-option (rest1 x) defining))
			(rest1 option)))
		 ((and (consp option) (get (first option) 'value-option-selector)))
		 ((null defining)
		  (format t "~%Warning: the file's option ~s is not recognized"
			  option))
		 (t ;;Used to signal an error here, but a warning seems more sensible.
		    (format t "~%Warning: While defining ~S,
~S is an option not recognized by DEFINE-PREDICATE"
                              defining option))))
	 (warn-if-unrecognized-option (rest1 options-left) defining))))

(deffun conjuncts-option-value (option conjuncts)
  (cond (conjuncts
	 (select (caar conjuncts)
	   (option (funcall (get option 'value-option-selector) (car conjuncts)))
	   ((':multiple) (or (disjuncts-option-value option (cdar conjuncts))
			     (conjuncts-option-value option (cdr conjuncts))))
	   (t (conjuncts-option-value option (cdr conjuncts)))))))

(deffun disjuncts-option-value (option disjuncts)
  (cond (disjuncts
	 (or (conjuncts-option-value option (cdar disjuncts))
	     (disjuncts-option-value option (cdr disjuncts))))))

#-prolog-micro-code
(defun %current-entrypoint (predicator definitions-location)
  (let ((definitions #-symbolics (DONT-OPTIMIZE (CDR definitions-location))
	             #+symbolics (contents definitions-location)))
    (definition-prover
      (cond ((eq (last-definition-universe definitions) *universe*)
	     (last-definition definitions))
	    ((find-and-cache-first-definition
	       definitions *universe* predicator))))))

(compile-flavor-methods clause)

;-------- For backward compatibility:

(defvar *definition-lock* nil "Need a lock for *definition* since it is exclusive.")

(defun set-definition (def)
  (process-lock (locf *definition-lock*))
  (setq *definition* def))

(defun unset-definition ()
  (prog1
    (definition-predicator *definition*)
    (process-unlock (locf *definition-lock*))))  

(defun add-definition-to-world (prover deterministic indexer predicator options
				clauses interpret-p indexes)
  (let ((*definition* (create-definition prover deterministic indexer predicator
					 (setq options (merge-options options *default-options*))
					 clauses interpret-p indexes)))
    (add-to-world predicator *definition*)))
			 
