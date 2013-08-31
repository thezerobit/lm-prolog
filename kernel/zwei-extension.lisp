;;; -*- Mode: Lisp; Package: Zwei; Base: 10. ; Patch-file:T -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;Belongs in compiler, but I didn't want to make it a patch file...
#+prolog-micro-code compiler:
(defun trivial-form-p (x)
  (or (symbolp x)
      (constantp x)
      (and (not (consp x))
	   (memq (car x) '(%reference %dereference)))))

;;First some stuff from old toplevel.

;Guess what language we're speaking!
(defun zwei-talking-to-prolog ()
  (cond ((eq *readtable* prolog:*prolog-readtable*))
	((boundp '*window*)
	 (let ((bp1 (FORWARD-DEFUN (BEG-LINE (POINT)) -1)))
	   (cond (bp1 (string-equal
			(bp-line bp1)
			"define-predicate" ':start1 1 ':end1 17.)))))))

(defun generally-defined (spec)
  (and (symbolp spec)
       (or (fdefinedp spec)
	   #+symbolics (get spec 'tv:compiled-only-arglist)
	   #-symbolics (get spec 'arglist)
	   (and (zwei-talking-to-prolog) (prolog:current-definition spec nil)))))

(defun general-argument-list (symbol)
  (cond ((zwei-talking-to-prolog)
	 (multiple-value-bind (arg-list found-p)
	     (prolog:predicate-argument-list symbol)
	   (cond (found-p arg-list) (t (arglist symbol)))))
        (t (arglist symbol))))

(defun general-documentation (symbol)
  (or
    (cond ((zwei-talking-to-prolog)
	   (or (prolog:predicate-documentation symbol) (documentation symbol)))
	  (t (documentation symbol #+(and (not symbolics) CommonLisp) 'function)))
    "No documentation found."))


(advise make-buffer-current :around update-prolog-defaults nil
  (let ((prolog:*add-world-when-loading* ':no))
      :do-it ;;we want its value
;;    (setq *defining-world-string*
;;        (string (prolog:option-value ':world prolog:*default-options*)))
      ))

#-(and (not CommonLisp) symbolics)
(advise-within add-patch-interval insert-interval :around include-default-options 0
  (let ((*file-default-options*
	  (MULTIPLE-VALUE-BIND (VARS VALS)
	      #+symbolics(fs:file-attribute-bindings *interval*)
	      #-symbolics(send *interval* ':attribute-bindings)
	    (PROGV VARS VALS prolog:*file-default-options*))))
    (cond (*file-default-options*
	   (let ((bp (INTERVAL-LAST-BP *PATCH-BUFFER*)))
	     (insert bp (format nil "~%/(compiler-let ((prolog:*file-default-options* '~s))~%"
				*file-default-options*))
	     :do-it
	     (insert bp "/)")))
	  (t :do-it))))

#+symbolics
(defmethod (lisp-syntax-mixin :additional-attributes) ()
  `((:BASE "Base" "~D")
    (:OPTIONS "Options" "~A")
    (:PACKAGE "Package" "~A")
    (:PATCH-FILE "Patch-File" "~A")))

(defcom com-prolog-macro-expand "Macroexpand the current region or definition,
as if it were seen by the interpreter." ()
  (com-reparse-attribute-list)
  (multiple-value-bind (vars vals)
      #+symbolics(fs:file-attribute-bindings *interval*)
      #-symbolics(send *interval* ':attribute-bindings)
      (progv vars vals
	(let (bp1 bp2)
	  (COND ((WINDOW-MARK-P *WINDOW*)
		 (SETQ BP1 (MARK) BP2 (POINT))
		 (OR (BP-< BP1 BP2) (PSETQ BP1 BP2 BP2 BP1)))
		((setq bp1 (DEFUN-INTERVAL (BEG-LINE (POINT)) 1 NIL NIL))
		 (SETQ BP2 (INTERVAL-LAST-BP BP1) BP1 (INTERVAL-FIRST-BP BP1)))
		(T
		 (BARF "Unbalanced parentheses")))
	  (LET ((STREAM (INTERVAL-STREAM bp1 bp2 t)))
	    (do ((FORM (READ STREAM '*EOF*) (READ STREAM '*EOF*)))
		((EQ FORM '*EOF*))
	      (grind-top-level (MACROEXPAND FORM)))))))
  DIS-NONE)


(defcom com-prolog-macro-expand-compiled "Macroexpand the current region or definition,
as if it were seen by the compiler." ()
  (let ((prolog:compile-p t))
    (com-prolog-macro-expand)))

(advise com-macro-expand-expression :around bind-attributes 0
  (multiple-value-bind (vars vals)
      #+symbolics(fs:file-attribute-bindings *interval*)
      #-symbolics(send *interval* ':attribute-bindings)
      (progv vars vals :do-it)))

(advise com-macro-expand-expression-all :around bind-attributes 0
  (multiple-value-bind (vars vals)
      #+symbolics(fs:file-attribute-bindings *interval*)
      #-symbolics(send *interval* ':attribute-bindings)
    (progv vars vals :do-it)))


#-symbolics prolog:
(advise-within zwei:com-documentation documentation :around prolog-top-level 0
  (multiple-value-bind (documentation defined-p)
      (predicate-documentation (first arglist))
    (cond ((and defined-p (zwei:ZWEI-TALKING-TO-PROLOG))
           documentation)
          (t :do-it))))

#-(and (not CommonLisp) symbolics) prolog:
(advise-within-each (#-symbolics zwei:com-quick-documentation
                     zwei:com-brief-documentation
                     zwei:com-long-documentation)
                    si:function-documentation :around prolog-top-level 0
  (multiple-value-bind (documentation defined-p)
      (predicate-documentation (first arglist))
    (cond ((and defined-p (zwei:ZWEI-TALKING-TO-PROLOG))
           documentation)
          (t :do-it))))

#-(and (not CommonLisp) symbolics) prolog:
(advise-within-each (#-symbolics zwei:com-quick-documentation
                     zwei:com-brief-documentation
                     zwei:com-long-documentation)
                    documentation :around prolog-top-level 0
  (multiple-value-bind (documentation defined-p)
      (predicate-documentation (first arglist))
    (cond ((and defined-p (zwei:ZWEI-TALKING-TO-PROLOG))
           documentation)
          (t :do-it))))

prolog:
(advise zwei:relevant-function-name :around prolog-top-level 0
  (cond ((zwei:zwei-talking-to-prolog) :do-it)
	((fourth arglist) :do-it)
	(t (zwei:relevant-function-name (first arglist)
					(second arglist)
					(third arglist)
					(or (fourth arglist) t)))))

#-(and (not CommonLisp) symbolics)
(prolog:advise-within-each (quick-arglist print-arglist)
                    arglist
                    :around prolog-top-level 0
  (general-argument-list (first arglist)))

#-(and (not CommonLisp) symbolics)
(prolog:advise-within-each (quick-arglist com-long-documentation)
		    fdefinedp :around prolog-top-level 0
  (generally-defined (first arglist)))

#+(and (not CommonLisp) symbolics)
(DEFCOM COM-BRIEF-DOCUMENTATION
        "Displays brief documentation for the specified Lisp function or LM-Prolog predicate.
By default, it displays documentation for the current function.  With a
numeric argument, it prompts for a function name, which you can either
type in or select with the mouse.  It displays the first line from the
summary paragraph in the echo area.  " ()
  (LET* ((DEF (RELEVANT-FUNCTION-NAME (POINT)))
         (NAME (IF *NUMERIC-ARG-P* (READ-FUNCTION-SPEC "Brief Document" DEF) DEF))
         (DOC (general-documentation NAME)))
    (COND ((NULL DOC) (TYPEIN-LINE "~S is not documented" NAME))
          (T (TYPEIN-LINE "~S: ~A" NAME
                          (NSUBSTRING DOC 0 (STRING-SEARCH-CHAR #\CR DOC))))))
  DIS-NONE)

#+(and (not CommonLisp) symbolics)
(DEFCOM COM-LONG-DOCUMENTATION
        "Displays the summary documentation for the specified function.
It prompts for a function name, which you can either type in or select with
the mouse.  The default is the current function.  " ()
  (modified-TYPEOUT-LONG-DOCUMENTATION (READ-FUNCTION-SPEC
					"Document"
					(RELEVANT-FUNCTION-NAME (POINT))))
  DIS-NONE)

#+(and (not CommonLisp) symbolics)
(DEFUN modified-TYPEOUT-LONG-DOCUMENTATION (NAME)
  (LET ((DOC (general-documentation NAME)))
    (COND ((NULL DOC) (TYPEIN-LINE "~S is not documented" NAME))
          (T (PRINT-ARGLIST NAME)
             (FORMAT T "~%~A" DOC)))))

(DEFCOM COM-SET-OPTIONS "Change LM-Prolog's default options
associated with this buffer or file.
Applies only to this buffer, and overrides what the attribute list says.
Queries you for whether to change the attribute list in the text as well.
The new value is read in the minibuffer."
  ()
  (let* ((package (symbol-package ':keyboard))
	 (options (TYPEIN-LINE-READ "Set options:")))
    (prolog:warn-if-unrecognized-option options "these options")	;7.12
    #+symbolics (SEND *INTERVAL* ':PUTPROP OPTIONS ':OPTIONS)
    #+symbolics (SET-ATTRIBUTE-INTERNAL
		  ':OPTIONS "Options" (FORMAT NIL "~S" OPTIONS) OPTIONS)
    #-symbolics (SEND *INTERVAL* ':SET-ATTRIBUTE ':options options ':QUERY)
    )
  #+symbolics DIS-TEXT #-symbolics DIS-NONE)


;;;ZLOG --- courtesy SYS: ZWEI; STREAM


(defflavor zlisp-mixin () ()
  (:required-flavors ztop-stream-mixin))
  
(defflavor zlog-mixin () ()
  (:required-flavors ztop-stream-mixin))

(defflavor zlisp-stream-from-window () (zlisp-mixin ztop-stream-from-window))

(defflavor zlog-stream-from-window () (zlog-mixin ztop-stream-from-window))

(DEFUN zlog-TOP-LEVEL (ZTOP-STREAM)
  (let ((prin1 *ztop-prin1*)
	(*package* (pkg-find-package :puser))
	(*ztop-package* (pkg-find-package :puser)))
    (DO-FOREVER
      (*CATCH 'ZTOP-TOP-LEVEL
	(prolog:prolog-TOP-LEVEL1 ZTOP-STREAM)))))

(DEFMETHOD (ZTOP-STREAM-MIXIN :AFTER :INIT) (ignore) ())

(DEFMETHOD (zlisp-MIXIN :AFTER :INIT) (INIT-PLIST)
  (SETQ *ZTOP-SG* (MAKE-STACK-GROUP "ZTOP" ':REGULAR-PDL-SIZE 40000
					   ':SPECIAL-PDL-SIZE 4000))
  (SETQ *STREAM-INPUT-HISTORY*
	(MAKE-HISTORY (STRING-APPEND "input history of "
				     (BUFFER-NAME (GET INIT-PLIST ':BUFFER)))))
  (INITIALIZE-ZTOP-SG SELF))

(DEFMETHOD (zlog-MIXIN :AFTER :INIT) (INIT-PLIST)
  (SETQ *ZTOP-SG* (MAKE-STACK-GROUP "ZTOP" ':REGULAR-PDL-SIZE 40000
					   ':SPECIAL-PDL-SIZE 4000))
  (SETQ *STREAM-INPUT-HISTORY*
	(MAKE-HISTORY (STRING-APPEND "input history of "
				     (BUFFER-NAME (GET INIT-PLIST ':BUFFER)))))
  (STACK-GROUP-PRESET *ZTOP-SG* `zlog-TOP-LEVEL self)
  (FUNCALL *ZTOP-SG*)
  (STREAM-REDISPLAY T))

(defvar *ztop-flavor-name* 'zlisp-stream-from-window)

(advise-within make-ztop-command-hook instantiate-flavor
	       :before replace-flavor-name nil
	       (setf (first arglist) *ztop-flavor-name*))

(defcom com-zlog-mode
	"Set up this buffer as a Prolog Listener."
	nil
  (let ((*ztop-flavor-name* 'zlog-stream-from-window))
    (pkg-goto :puser)
    (SEND *INTERVAL* ':SET-ATTRIBUTE ':PACKAGE "PUSER" NIL)
    (SETF (BUFFER-PACKAGE *INTERVAL*) *PACKAGE*)
    (turn-off-mode *major-mode*)
    (dolist (mode *unsticky-minor-modes*) (turn-off-mode mode))
    (turn-on-mode 'ztop-mode))
  dis-none)

(compile-flavor-methods
  zlisp-stream-from-window zlog-stream-from-window)

(SET-COMTAB *STANDARD-COMTAB*
	    ()
            '(("Set Options" . com-set-options)
	      ("Zlog Mode" . com-zlog-mode)
	      ("Prolog Macro Expand" . com-prolog-macro-expand)
	      ("Prolog Macro Expand Compiled" . com-prolog-macro-expand-compiled)))

