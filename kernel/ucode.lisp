;;; -*- Mode: Lisp; Package: Compiler; Base: 8. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


(EVAL-WHEN  (COMPILE EVAL LOAD)
  (READFILE "LMP:KERNEL;DEFMIC-PROLOG" "PROLOG" T))

#+cadr
(progn 'compile

(defun insure-locative-even ()
  (cond ((evenp dtp-locative)
	 (format t "~%YOU ARE GOING TO LOSE! The microcode depends on DTP-LOCATIVE being odd. ~
                  ~%Fix it by changing BIT-SET to BIT-CLEAR at appropriate places in ~
		  LMP:KERNEL;UC-PROLOG"))))

(insure-locative-even)

UA:
(DEFUN-IN-MICROCODE PROLOG:(MICROCODE-1 MICROCODE-2 MICROCODE-3
			    MICROCODE-4 MICROCODE-5 MICROCODE-6)
		    . #.UC-PROLOG)

;;;Stuff for compiler/microcompiler.

(DEFUN (:PROPERTY LIST-IN-AREA P2) (ARGLIST DESTINATION)
  (COND ((EQ (FIRST ARGLIST) 'PROLOG:*PROLOG-WORK-AREA*)
	 (cond #+cadr
	       ((NOT GENERATING-MICRO-COMPILER-INPUT-P)
		(p2 `(prolog:%prolog-list ,@(REST1 ARGLIST) ',(1- (LENGTH ARGLIST)))
		    destination))
	       (T 
		(P2MISC 'PROLOG:%PROLOG-LIST `(,@(REST1 ARGLIST) ',(1- (LENGTH ARGLIST)))
			DESTINATION
			(LENGTH ARGLIST)))))
	(T (P2ARGC 'LIST-IN-AREA ARGLIST (GETARGDESC 'LIST-IN-AREA) DESTINATION
		   'LIST-IN-AREA))))

(DEFUN (:PROPERTY LIST*-IN-AREA P2) (ARGLIST DESTINATION)
  (COND ((EQ (FIRST ARGLIST) 'PROLOG:*PROLOG-WORK-AREA*)
	 (cond #+cadr
	       ((NOT GENERATING-MICRO-COMPILER-INPUT-P)
		(p2 `(prolog:%prolog-list* ,@(REST1 ARGLIST) ',(1- (LENGTH ARGLIST)))
		    destination))
	       (T 
		(P2MISC 'PROLOG:%PROLOG-LIST* `(,@(REST1 ARGLIST) ',(1- (LENGTH ARGLIST)))
			DESTINATION
			(LENGTH ARGLIST)))))
	(T (P2ARGC 'LIST*-IN-AREA ARGLIST (GETARGDESC 'LIST*-IN-AREA) DESTINATION
		   'LIST*-IN-AREA))))

(defmacro def-p2fn (fn alias opcode)
  `(progn 'compile
	  (defprop ,fn ,alias p2fn)
	  (defprop ,alias ,opcode qlval)))

;;Old systems use opcodes 16<0..7> and 17<0..2>
;;New systems use opcodes 17<0..3>, 37<0..3>, and 21<0..2>.


(DEF-P2FN PROLOG:%reference *reference
  #-Commonlisp 16000 #+Commonlisp 17000)
(DEF-P2FN PROLOG:%dereference *dereference
  #-Commonlisp 36000 #+Commonlisp 37000)
(DEF-P2FN PROLOG:%cell *cell
  #-Commonlisp 56000 #+Commonlisp 57000)
(DEF-P2FN PROLOG:%unify-term-with-term *unify-term-with-term
  #-Commonlisp 76000 #+Commonlisp 77000)
(DEF-P2FN PROLOG:%unify-term-with-template *unify-term-with-template
  #-Commonlisp 116000 #+Commonlisp 117000)
(DEF-P2FN PROLOG:%current-entrypoint *current-entrypoint
  #-Commonlisp 136000 #+Commonlisp 137000)
(DEF-P2FN PROLOG:%invoke *invoke
  #-Commonlisp 156000 #+Commonlisp 157000)
(DEF-P2FN PROLOG:%untrail *untrail
  #-Commonlisp 176000 #+Commonlisp 177000) 
(DEF-P2FN PROLOG:%prolog-list *prolog-list
  #-Commonlisp 17000 #+Commonlisp 21000)
(DEF-P2FN PROLOG:%prolog-list* *prolog-list*
  #-Commonlisp 37000 #+Commonlisp 61000)
(DEF-P2FN PROLOG:%cell0 *cell0
  #-Commonlisp 57000 #+Commonlisp 121000)


(mapc 'putprop
      'prolog:(%reference %dereference %cell
	       %unify-term-with-term %unify-term-with-template %current-entrypoint
	       %invoke %untrail
	       %prolog-list %prolog-list* %cell0)
      (circular-list 'p2prolog)
      (circular-list 'p2))

(defun p2-source-hack (form dest)
  (let ((source (p2-source form dest))
	(last (array-pop #-CommonLisp #'qcmp-output #+CommonLisp qcmp-output)))
    (cond ((and (equal source '(pdl-pop))
		(eq (car last) 'move)
		(eq (cadr last) 'd-pdl))
	   (caddr last))
	  (t (array-push #-CommonLisp #'qcmp-output #+CommonLisp qcmp-output last)
	     source))))

(DEFUN p2prolog (ARGL DEST)
  (COND ((OR (NEQ DEST 'D-PDL)			;Otherwise MISC is better
	     GENERATING-MICRO-COMPILER-INPUT-P)
	 (P2MISC P2FN ARGL DEST (LENGTH ARGL)))
	(T
	 (mapc 'p2push (butlast argl))
	 (selectq p2fn
	   (prolog:%prolog-list
	    (outi `(*prolog-list 0 ,(cadar (last argl)))))
	   (prolog:%prolog-list*
	    (outi `(*prolog-list* 0 ,(cadar (last argl)))))	;imm arg
	   (prolog:%cell0
	    (outi `(*cell0 0 (quote-vector 'nil))))
	   (t (outi `(,(get p2fn 'p2fn) 0 ,(p2-source-hack (car (last argl)) 'd-pdl))))))))

#-CommonLisp
(defun disassemble-instruction-1 (fef pc)
  (let* ((WD (#-Symbolics DISASSEMBLE-FETCH #+Symbolics FEF-INSTRUCTION FEF PC))
	 (OP (LDB 1104 WD))
	 (SUBOP (LDB 1503 WD))
	 (DISP (LDB 0011 WD))
	 (REG (LDB 0603 WD)))
    (selectq op
      (16
       (selectq SUBOP
	 (0 (format t "~O REFERENCE d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (1 (format t "~O DEREFERENCE d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (2 (format t "~O CELL d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (3 (format t "~O UNIFY-WITH-TERM d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (4 (format t "~O UNIFY-WITH-TEMPLATE d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (5 (format t "~O CURRENT-ENTRYPOINT d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (6 (format t "~O INVOKE d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (5 (format t "~O UNTRAIL d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)))
      (17
       (selectq SUBOP
	 (0 (format t "~O PROLOG-LIST d-pdl, ~D long" pc disp) 1)
	 (1 (format t "~O PROLOG-LIST* d-pdl, ~D long" pc disp) 1)
	 (2 (format t "~O CELL0 d-pdl" pc) 1))))))

#+CommonLisp
(defun disassemble-instruction-1 (fef pc)
  (let* ((WD (#-Symbolics DISASSEMBLE-FETCH #+Symbolics FEF-INSTRUCTION FEF PC))
	 (OP (LDB 1104 WD))
	 (SUBOP (LDB 1503 WD))
	 (DISP (LDB 0011 WD))
	 (REG (LDB 0603 WD)))
    (selectq op
      (17
       (selectq SUBOP
	 (0 (format t "~3D REFERENCE d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (1 (format t "~3D DEREFERENCE d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (2 (format t "~3D CELL d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (3 (format t "~3D UNIFY-WITH-TERM d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (4 (format t "~3D UNIFY-WITH-TEMPLATE d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (5 (format t "~3D CURRENT-ENTRYPOINT d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (6 (format t "~3D INVOKE d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)
	 (5 (format t "~3D UNTRAIL d-pdl" pc)
	    (DISASSEMBLE-ADDRESS FEF REG DISP)
	    1)))
      (1
       (selectq SUBOP
	 (1 (format t "~3D PROLOG-LIST d-pdl, ~D long" pc disp) 1)
	 (3 (format t "~3D PROLOG-LIST* d-pdl, ~D long" pc disp) 1)
	 (5 (format t "~3D CELL0 d-pdl" pc) 1))))))

(ADVISE DISASSEMBLE-INSTRUCTION :AROUND OPCODES-16-17 NIL
	(OR (APPLY 'DISASSEMBLE-INSTRUCTION-1 ARGLIST) :DO-IT))

(COMPILE-ENCAPSULATIONS 'DISASSEMBLE-INSTRUCTION)

(DEFPROP PROLOG:%CELL LMP-CELL LAST-ARG-IN-T-ENTRY)
(DEFPROP PROLOG:%REFERENCE LMP-REFERENCE LAST-ARG-IN-T-ENTRY)
(DEFPROP PROLOG:%DEREFERENCE LMP-DEREFERENCE LAST-ARG-IN-T-ENTRY)
(DEFPROP PROLOG:%UNIFY-TERM-WITH-TERM LMP-UPDL LAST-ARG-IN-T-ENTRY)
(DEFPROP PROLOG:%CURRENT-ENTRYPOINT LMP-CENTRY LAST-ARG-IN-T-ENTRY)
(DEFPROP PROLOG:%INVOKE LMP-INVOKE LAST-ARG-IN-T-ENTRY)

(cond ((fdefinedp 'mc-3)
       (ADVISE MC-3 :AROUND "PROLOG INSTRUCTIONS" 0
	 (OR (APPLY #'MC-3-PROLOG ARGLIST) :DO-IT))))

(DEFUN MC-3-PROLOG (WD)
  (COND ((AND (CONSP WD) (CONSP (CDR WD)) (CONSP (CDDR WD)))
	 (LET ((OP (CAR WD)) (DEST (CADR WD)) (ADR (CADDR WD)))
	   (SELECTQ OP
	     #-Lambda
	     (PROLOG:(%REFERENCE %DEREFERENCE)	;New CXR-like instructions
	      (GET-ADR-IN-T ADR)
	      (SETQ TP-IN-T-FLAG 'D-PDL)
	      (MC-CALL-OUT 1 '((ARGS 1)) 'MISC-ENTRY OP)
	      (STORE-T-IN-DEST DEST)
	      T)
	     (MISC
	      (COND (;Miscs with varying # args
		     (MEMQ ADR 'PROLOG:(%PROLOG-LIST %PROLOG-LIST*))
		     ;last arg was 1- # args...
		     (LET ((NARGS (1+ (CADR (CADDR MC-LAST-OUT)))))
		       (MC-CALL-OUT NARGS '((ARGS NARGS)) 'MISC-ENTRY ADR)
		       (POP-SLOTLIST NARGS 'D-PDL)
		       (STORE-T-IN-DEST DEST)
		       T)))))))))

)

PROLOG:
(PROGN 'COMPILE

(DEFVAR LEXICAL-BIT #-lexical 0 #+lexical 4)

(DEFVAR CIRCULARITY-MODE-BITS #-lexical 0 #+lexical 4
  "Forwards to an A-Mem location that controls circularity mode.
 0=ignore, 1=prevent, 2=handle, 4=lexical.")

(DEFUN FORWARD-IVC-TO-A-MEM (SYMBOL A-MEM-LOC)
  ;;Dont want no cdr-code in A-MEM
  (%P-STORE-TAG-AND-POINTER (+ A-MEM-LOC SYS:A-MEMORY-VIRTUAL-ADDRESS)
			    (%DATA-TYPE (SYMEVAL SYMBOL))
			    (SYMEVAL SYMBOL))
  (%P-STORE-TAG-AND-POINTER (VALUE-CELL-LOCATION SYMBOL)
			    DTP-ONE-Q-FORWARD
			    (+ A-MEM-LOC SYS:A-MEMORY-VIRTUAL-ADDRESS)))

;;*TRAIL-ARRAY* and *PROLOG-WORK-AREA* can be in A-MEM, since they are per window,
;;and will be restored after warm boot. *UNIVERSE* would be lost upon warm boot
;;if it were in A-MEM.


(DEFVAR *EXIT-VECTOR-ARRAY* NIL)

; Courtesy SYS: MICRO-COMPILER; MLAP LISP >
(DEFUN INITIALIZE-EXIT-VECTOR ()
  (declare (special compiler:*mc-exit-vector-array*))
  (%p-store-tag-and-pointer (value-cell-location 'compiler:*mc-exit-vector-array*)
			    dtp-one-q-forward
			    (locf *exit-vector-array*))
  (COND ((NULL *EXIT-VECTOR-ARRAY*)
	 (SETQ *EXIT-VECTOR-ARRAY*
	       (MAKE-ARRAY 1000
			   ':TYPE 'ART-Q-LIST
			   ':AREA si:control-tables
			   ':LEADER-LIST '(0))))
	(T (STORE-ARRAY-LEADER 0 *EXIT-VECTOR-ARRAY* 0)))
  (SETQ SI:%MC-CODE-EXIT-VECTOR (locf (aref *exit-vector-array* 0))))

(defun assure-linkage-alist-loaded (&optional (ver si:%microcode-version-number))
  (cond ((= ver (get (locf COMPILER:*UCADR-STATE-LIST*) 'compiler:version-number)) t)
        (t (let ((pathname
		    (SELECT-PROCESSOR
		     (:CADR (SEND (FS:PARSE-PATHNAME "SYS: UBIN; UCADR") ':new-pathname
				  ':type "SYM"
				  ':version ver))
		     (:LAMBDA (SEND (FS:PARSE-PATHNAME "SYS: UBIN; ULAMBDA") ':new-pathname
				    ':type "LMC-SYM"
				    ':version ver))
		     (:explorer (send (fs:parse-pathname "SYS: UBIN; ULAMBDA") ':new-pathname
				      ':type "EMC-SYM"
				      ':version ver)
		     )))
		 (DEFAULT-CONS-AREA WORKING-STORAGE-AREA)
		 (IBASE 8))
	     (LET-IF (NOT (PROBEF PATHNAME))
		     ((PATHNAME (SEND PATHNAME ':NEW-PATHNAME ':NAME "ULAMBDA-PROLOG")))
	       (PKG-BIND "COMPILER"
		 (WITH-OPEN-FILE (STREAM PATHNAME ':DIRECTION ':INPUT)
		   (PROG (ITEM ASSEMBLER-STATE)
		      COM0
			 (COND ((NOT (< (SETQ ITEM (READ STREAM)) 0))
				(GO COM0)))
		      COM
			 (COND ((= ITEM -1) (GO FIN))
			       ((= ITEM -2) (GO FIN))  ;ignore
			       ((= ITEM -4)
				(SETQ ASSEMBLER-STATE (READ STREAM))
				(GO FIN))
			       (T (FERROR NIL "~O is not a valid block header" ITEM)))
		      FIN
			 (SETQ COMPILER:*UCADR-STATE-LIST* ASSEMBLER-STATE)
			 (RETURN)))
		 (SETQ COMPILER:*MC-LINKAGE-ALIST*
		       (GET (locf COMPILER:*UCADR-STATE-LIST*) 'COMPILER:MC-LINKAGE-ALIST))
		 T))))))

(defun get-mc-linkage (x)
  (assure-linkage-alist-loaded)
  (or (third (assq x compiler:*mc-linkage-alist*))
      (ferror nil "~%The microcode symbol ~S, needed by LM-Prolog, was not found.~
                   ~%You need to get an updated version of the microcode from LMI."
	      x)))

(defvar *unify-dispatch-table*
	(make-pixel-array 40 40 ':type 'art-q ':AREA si:control-tables))

(defun initialize-dispatch-table ()
  (%p-store-tag-and-pointer (+ (get-mc-linkage 'compiler:a-unify-dispatch) si:a-memory-virtual-address)
			    dtp-locative
			    (ap-1-force *unify-dispatch-table* 0))
  (let ((lmpu-fail (get-mc-linkage 'compiler:lmp-pop-fail))
	(lmpu-x-x (get-mc-linkage 'compiler:lmpu-x-x))
	(lmpu-instance-x (get-mc-linkage 'compiler:lmpu-instance-x))
	(lmpu-x-instance (get-mc-linkage 'compiler:lmpu-x-instance))
	(lmpu-var-x (get-mc-linkage 'compiler:lmpu-var-x))
	(lmpu-x-var (get-mc-linkage 'compiler:lmpu-x-var))
	(lmpu-var-var (get-mc-linkage 'compiler:lmpu-var-var))
	(lmpu-var-list (get-mc-linkage 'compiler:lmpu-var-list))
	(lmpu-list-var (get-mc-linkage 'compiler:lmpu-list-var))
	(lmpu-list-list (get-mc-linkage 'compiler:lmpu-list-list)))
    (dotimes (x 40)
      (dotimes (y 40)
	(as-2-reverse (if (= x y) lmpu-x-x lmpu-fail) *unify-dispatch-table* x y)))
    (dotimes (x 40)
      (as-2-reverse lmpu-instance-x *unify-dispatch-table* x dtp-instance)
      (as-2-reverse lmpu-x-instance *unify-dispatch-table* dtp-instance x))
    (dotimes (x 40)
      (as-2-reverse lmpu-var-x *unify-dispatch-table* x dtp-locative)
      (as-2-reverse lmpu-x-var *unify-dispatch-table* dtp-locative x))
    (as-2-reverse lmpu-var-var *unify-dispatch-table* dtp-locative dtp-locative)
    (as-2-reverse lmpu-var-list *unify-dispatch-table* dtp-list dtp-locative)
    (as-2-reverse lmpu-list-var *unify-dispatch-table* dtp-locative dtp-list)
    (as-2-reverse lmpu-list-list *unify-dispatch-table* dtp-list dtp-list)))

(DEFUN MICROCODE-0 ()
    (INITIALIZE-EXIT-VECTOR)
    (INITIALIZE-DISPATCH-TABLE)
    (SETQ CIRCULARITY-MODE-BITS LEXICAL-BIT) ;;Missing in RESET-PROLOG
    (FORWARD-IVC-TO-A-MEM '*VECTOR* (get-mc-linkage 'compiler:a-lmp-vector))
    (FORWARD-IVC-TO-A-MEM '*TRAIL-ARRAY* (get-mc-linkage 'compiler:a-lmp-trail))
    (FORWARD-IVC-TO-A-MEM '*PROLOG-WORK-AREA* (get-mc-linkage 'compiler:a-lmp-area))
    (FORWARD-IVC-TO-A-MEM 'CIRCULARITY-MODE-BITS (get-mc-linkage 'compiler:a-lmp-mode))
#+cadr    (ASET ':CAR *EXIT-VECTOR-ARRAY* 763)
#+cadr    (ASET ':CDR *EXIT-VECTOR-ARRAY* 764)
    (ASET ':UNIFY *EXIT-VECTOR-ARRAY* 765)
    (ASET 'OCCURS-IN *EXIT-VECTOR-ARRAY* 766)
    (ASET '%UNIFY-TERM-WITH-TEMPLATE *EXIT-VECTOR-ARRAY* 767)
    (ASET '%CONSTRUCT *EXIT-VECTOR-ARRAY* 770)
    (ASET '%UNIFY-TERM-WITH-TERM *EXIT-VECTOR-ARRAY* 771)
    (ASET 'ARRAY-PUSH-EXTEND *EXIT-VECTOR-ARRAY* 772)
    (ASET (%MAKE-POINTER DTP-EXTERNAL-VALUE-CELL-POINTER
			 (LOCF (GET 'READ-ONLY-VARIABLE 'SI:FLAVOR)))
	  *EXIT-VECTOR-ARRAY*
	  773)
    (ASET 'TRUE *EXIT-VECTOR-ARRAY* 774)
    (ASET 'FALSE *EXIT-VECTOR-ARRAY* 775)
    (ASET 'FIND-AND-CACHE-FIRST-DEFINITION *EXIT-VECTOR-ARRAY* 776)
    (FORWARD-IVC-TO-A-MEM '*UNIVERSE*
			  (- (%POINTER (ALOC *EXIT-VECTOR-ARRAY* 777))
			     SYS:A-MEMORY-VIRTUAL-ADDRESS))
    T)

(DEFUN INSTALL-CIRCULARITY-MODE-IGNORE ()
  (SETQ CIRCULARITY-MODE-BITS LEXICAL-BIT))

(DEFUN INSTALL-CIRCULARITY-MODE-PREVENT ()
  (SETQ CIRCULARITY-MODE-BITS (+ 1 LEXICAL-BIT)))

(DEFUN INSTALL-CIRCULARITY-MODE-HANDLE ()
  (SETQ CIRCULARITY-MODE-BITS (+ 2 LEXICAL-BIT)))

;; This is handy and is expected by constraints, at least.
(DEFSUBST UNIFY (X Y) (%UNIFY-TERM-WITH-TERM X Y))

;; Random places outside of unifier call this.
(DEFSUBST OCCUR-CHECK (X Y) (NOT (OCCURS-IN X Y)))

(DEFUN LOAD-MICROCODE ()
  (MICROCODE-0)
  #+cadr
  (PROGN (MICROCODE-1)
	 (MICROCODE-2)
	 (MICROCODE-3)
	 (MICROCODE-4)
	 (MICROCODE-5)
	 (MICROCODE-6)
	 #-CommonLisp UA:
	 (PROGN
	   (MODIFY-DISPATCH-TABLE CC:OPDTB 16 ((MC-LINKAGE LMP-NODEST)))
	   (MODIFY-DISPATCH-TABLE CC:OPDTB 17 ((MC-LINKAGE LMP-NODEST-NOSOURCE)))
	   (MODIFY-DISPATCH-TABLE CC:CAR-PRE-DISPATCH #.DTP-INSTANCE
				  (INHIBIT-XCT-NEXT-BIT (MC-LINKAGE LMP-SEND-CAR)))
	   (MODIFY-DISPATCH-TABLE CC:CDR-PRE-DISPATCH #.DTP-INSTANCE
				  (INHIBIT-XCT-NEXT-BIT (MC-LINKAGE LMP-SEND-CDR))))
	 #+CommonLisp UA:
	 (PROGN
	   (MODIFY-DISPATCH-TABLE CC:OPDTB 17 ((MC-LINKAGE LMP-NODEST)))
	   (MODIFY-DISPATCH-TABLE CC:OPDTB 37 ((MC-LINKAGE LMP-NODEST)))
	   (MODIFY-DISPATCH-TABLE CC:OPDTB 21 ((MC-LINKAGE LMP-NODEST-NOSOURCE))))
	 ))

(LOAD-MICROCODE)

#-cadr
(progn 'compile
(defun occurs-in (key term) (occurs-in key term))

(defun %cell0 () (%cell0))

(defun %untrail (mark) (%untrail mark))

(defun %unify-term-with-term (term-1 term-2) (%unify-term-with-term term-1 term-2))

(defun %construct (template) (%construct template))

(defun %unify-term-with-template (term template) (%unify-term-with-template term template))

(defun %cell (variable-name) (%cell variable-name))

(defun %reference (term) (%reference term))

(defun %dereference (term) (%dereference term))

(defun %invoke (cont) (%invoke cont))

(defun %current-entrypoint (predicator alist-location)
  (%current-entrypoint predicator alist-location))

))
