;;; -*- Mode: Lisp; Package: User; Base: 10. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;This defines LM-Prolog system of Ken Kahn and Mats Carlsson

;;This file is the only one that needs to be modified to for different sites.

;;Distinguish between old and new Lisp systems.
(cond ((neq 'user:x ':x) (sstatus feature COMMONLISP)))

;;To install LM-Prolog do the following:
;;======================================

;;For Lambdas and Explorers, the Prolog microcode is assumed to be
;; present in the system microcode.

;;For CADR/LM2, the microcode is compiled incrementally.

;;For 3600, there is no microcode yet.
#-3600
(sstatus feature PROLOG-MICRO-CODE)

#+(and (not cadr) commonlisp (not Symbolics))
(sstatus feature LEXICAL)

;;Finally load this file and do (LOAD-PROLOG ':RECOMPILE)

;;To make sure LM-Prolog works properly, load LMP:LIBRARY;TEST and
;;type (PROLOG:TEST ?) and (WITH-WORLD :INTERPRETED-TESTS (PROLOG:TEST ?)) to Prolog.

;;To save a band, cold-boot the machine and log in as LM-Prolog.
;;It will load all binaries.  Then disk-save.

;;To start up LM-Prolog do the following:
;;=======================================
;;(LOGIN "LM-Prolog") 
;;typing † will give you a little help
;;try running (DEMOS) in Prolog for examples and to add in optional features

;;Whether or not demo files are recompiled is controlled by the variable
;;PROLOG:*COMPILE-IF-NEEDED*. Its value can be :YES, :NO, or :QUERY.
;;The default is :NO.

;(let ((h (send fs:fdefine-file-pathname ':host)))
;  (and (typep h 'fs:logical-host) (setq h (send h ':host)))
;  (cond ((fdefinedp 'fs:set-logical-pathname-host)
;	 (fs:set-logical-pathname-host "LMP"
;	  :physical-host h
;	  :translations
;	  '(("SYSTEM;"
;	     #-symbolics "lm-prolog;" #+symbolics ">lm-prolog>")
;	    ("COMPATIBILITY;"
;	     #-symbolics "lm-prolog.compatibility;" #+symbolics ">lm-prolog>compatibility>")
;	    ("EXPERIMENTAL;"
;	     #-symbolics "lm-prolog.experimental;" #+symbolics ">lm-prolog>experimental>")
;	    ("KERNEL;"
;	     #-symbolics "lm-prolog.kernel;" #+symbolics ">lm-prolog>kernel>")
;	    ("LIBRARY;"
;	     #-symbolics "lm-prolog.library;" #+symbolics ">lm-prolog>library>")
;	    ("PREDICATES;"
;	     #-symbolics "lm-prolog.predicates;" #+symbolics ">lm-prolog>predicates>"))))
;	(t (fs:add-logical-pathname-host "LMP" h
;	    '(("SYSTEM"
;	       #-symbolics "lm-prolog;" #+symbolics ">lm-prolog>")
;	      ("COMPATIBILITY"
;	       #-symbolics "lm-prolog.compatibility;" #+symbolics ">lm-prolog>compatibility>")
;	      ("EXPERIMENTAL"
;	       #-symbolics "lm-prolog.experimental;" #+symbolics ">lm-prolog>experimental>")
;	      ("KERNEL"
;	       #-symbolics "lm-prolog.kernel;" #+symbolics ">lm-prolog>kernel>")
;	      ("LIBRARY"
;	       #-symbolics "lm-prolog.library;" #+symbolics ">lm-prolog>library>")
;	      ("PREDICATES"
;	       #-symbolics "lm-prolog.predicates;" #+symbolics ">lm-prolog>predicates>"))))))

(cond ((not (status feature lm-prolog))
       (load "lmp:system;global lisp")))

;;This is handy if you have e.g. versions with and without microcode on the same directory.
(DEFVAR default-binary-file-type
      #-symbolics "QFASL" #+(and symbolics (not 3600)) "QBIN" #+3600 "BIN")

;;#+lexical 				;;this is up to you
;;(setq default-binary-file-type "QFASL-LEXICAL")

#+(and symbolics prolog-micro-code) (load "SYS:SYS;UADEFS")

;;Don't break while reading out-conditionalized code.
#+symbolics (package-declare eh global 100)
#-symbolics (package-declare dbg global 100)

(defsystem lm-prolog
  (:pathname-default "lmp:kernel;")
  #-symbolics (:default-binary-file-type #.default-binary-file-type)
  (:patchable "lmp:system;")
  (:package prolog)
  (:name "LM-Prolog")
  (:module destructuring-let "dlet") 
  (:module recursion-removal "remrec")
  (:module support-for-support "pre-support")
  (:module support "support")
  (:module trail "trail")
  (:module db-support "db-support")
  (:module editor-extensions-for-prolog "zwei-extension" :package zwei)
  #-prolog-micro-code (:module ucode "instead-of-ucode")
  #+prolog-micro-code (:MODULE SUPPORT-FOR-UCODE "PRE-UCODE" :PACKAGE UA)
  #+prolog-micro-code (:MODULE UCODE "UCODE" :PACKAGE COMPILER)
  (:module compiler "compiler")
  (:module theorem-prover "prove")
  (:module top-level "toplevel")
  #-symbolics (:module error-handler "peh" :package eh)
  (:module control-primitives "lmp:predicates;control")
  (:module lazy-collections "lmp:predicates;lazy")
  (:module utility-primitives "lmp:predicates;utilities")
  (:module customize-primitives "lmp:predicates;customize")
  (:module database-primitives "lmp:predicates;database")
  (:module top-levels "lmp:predicates;toplevels")
  (:module loaded "lmp:system;loaded")
  ;;top levels written in LM-Prolog
  (:module trace-facility "lmp:predicates;trace")
  (:module demo-menu "lmp:library;demos")
  (:compile-load destructuring-let)
  (:compile-load recursion-removal (:fasload destructuring-let) (:fasload destructuring-let))
  (:compile-load support-for-support (:fasload recursion-removal) (:fasload recursion-removal))
  #-prolog-micro-code
  (:COMPILE-LOAD UCODE
		 (:FASLOAD SUPPORT-FOR-SUPPORT) (:FASLOAD SUPPORT-FOR-SUPPORT))
  #+prolog-micro-code
  (:SKIP :FASLOAD
	 (:COMPILE SUPPORT-FOR-UCODE (:FASLOAD SUPPORT-FOR-SUPPORT)))
  #+prolog-micro-code
  (:COMPILE-LOAD UCODE
		 ((:COMPILE SUPPORT-FOR-UCODE) (:FASLOAD SUPPORT-FOR-SUPPORT SUPPORT-FOR-UCODE))
		 (:FASLOAD SUPPORT-FOR-SUPPORT))
  (:compile-load support (:fasload ucode) (:fasload ucode))
  (:compile-load trail (:fasload support) (:fasload support))
  (:compile-load theorem-prover (:fasload trail) (:fasload trail))
  (:compile-load db-support (:fasload theorem-prover) (:fasload theorem-prover))
  (:compile-load compiler (:fasload db-support) (:fasload db-support))
  (:compile-load top-level (:fasload compiler) (:fasload compiler))
  #-symbolics (:compile-load error-handler (:fasload top-level) (:fasload top-level))
  (:compile-load editor-extensions-for-prolog (:fasload top-level))
  (:compile-load lazy-collections
   (:fasload top-level)
   (:fasload top-level))
  (:compile-load control-primitives
   (:fasload top-level lazy-collections)
   (:fasload top-level))
  (:compile-load utility-primitives 
   (:fasload top-level control-primitives lazy-collections)
   (:fasload top-level))
  (:compile-load customize-primitives
   (:fasload top-level control-primitives lazy-collections utility-primitives)
   (:fasload top-level))
  (:compile-load database-primitives
   (:fasload top-level control-primitives lazy-collections utility-primitives)
   (:fasload top-level))
  (:compile-load top-levels
   (:fasload top-level control-primitives lazy-collections utility-primitives)
   (:fasload top-level))
  (:compile-load trace-facility
   (:fasload top-level control-primitives lazy-collections utility-primitives)
   (:fasload top-level))
  (:compile-load demo-menu (:fasload top-level) (:fasload top-level))
  (:readfile loaded (:fasload demo-menu)))

; For tags searches.
(defsystem prolog-sources
  (:package prolog)
  (:module control-primitives "lmp:predicates;control")
  (:module lazy-collections "lmp:predicates;lazy")
  (:module utility-primitives "lmp:predicates;utilities")
  (:module customize-primitives "lmp:predicates;customize")
  (:module database-primitives "lmp:predicates;database")
  (:module top-levels "lmp:predicates;toplevels")
  (:module loaded "lmp:system;loaded")
  (:module trace-facility "lmp:predicates;trace")
  (:module demo-menu "lmp:library;demos")
  (:compile-load control-primitives)
  (:compile-load lazy-collections)
  (:compile-load utility-primitives)
  (:compile-load customize-primitives)
  (:compile-load database-primitives)
  (:compile-load top-levels)
  (:compile-load loaded)
  (:compile-load trace-facility)
  (:compile-load demo-menu)
  )

(defun backup-prolog ()
  (fs:mt-reset)
  (fs:copy-directory "sys: cold; defmic-prolog" "MT:" :copy-only :newest :copy-subdirectories nil)	;internal use only
  (fs:copy-directory "sys: ulambda; ucode" "MT:" :copy-only :newest :copy-subdirectories nil)	;internal use only
  (fs:copy-directory "sys: ulambda; uc-prolog" "MT:" :copy-only :newest :copy-subdirectories nil)	;internal use only
  (fs:copy-directory "sys: site; lm-prolog system" "MT:" :copy-only :newest :copy-subdirectories nil)
  (fs:copy-directory "sys: ubin; ulambda-prolog" "MT:" :copy-only :newest :copy-subdirectories nil)
  (fs:copy-directory "lama: release-3.lm-prolog;" "MT:" :copy-only :newest)
  (fs:mt-write-eof)
  (fs:mt-unload))


;Load LM-Prolog with minimal fuss.
(defun load-prolog (&rest make-system-args)
  (let ((system-name ':LM-prolog))
    #+(and symbolics prolog-micro-code)
      (cond (make-system-args (pkg-bind "UA" (make-system ':micro-assembler))))
    (lexpr-funcall #'make-system system-name
		   ':no-reload-system-declaration ':no-increment-patch ':noconfirm
		   make-system-args)))

(globalize 'load-prolog)

