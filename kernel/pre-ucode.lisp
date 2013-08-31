;;; -*- Mode:LISP; Package:UA; Base:8 -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


#+cadr
(PROGN 'COMPILE

CC:
(DEFUN CC-LINKAGE (LABEL)
  (LET* ((REG-ADR (CC-LOOKUP-NAME LABEL))
         (RANGE-NAME (CC-FIND-REG-ADR-RANGE REG-ADR))
         (RANGE-BASE (SYMEVAL (GET RANGE-NAME 'CC-LOWEST-ADR)))
         (MEM (SELECTQ RANGE-NAME
                (A 'UA:A-MEM)
                (M 'UA:M-MEM)
                (D 'UA:D-MEM)
                (C 'UA:I-MEM)))
         (MULT
           (SELECTQ RANGE-NAME
             (A 'UA:A-SOURCE-MULTIPLIER)
             (M 'UA:M-SOURCE-MULTIPLIER)
             (D 'UA:DISPATCH-ADDRESS-MULTIPLIER)
             (C 'UA:JUMP-ADDRESS-MULTIPLIER))))
    (UA:CONS-LAP-EVAL `(,MEM (UA:FIELD ,MULT ,(- REG-ADR RANGE-BASE))))))

(prolog:deffun form-groups (forms count max sofar)
  (cond ((null forms) (list sofar))
        ((= count max) (cons sofar (form-groups forms 0 max ())))
        (t (form-groups (cdr forms) (1+ count) max (cons (car forms) sofar)))))

(DEFMACRO DEFUN-IN-MICROCODE (NAMES &BODY SOURCE)
  (DECLARE (SPECIAL UCADR-STATE-LIST))
  (PKG-BIND "UA"
    (LET* ((IBASE 8.)
	   (BASE 8.)
	   (FORMS ())
	   (SLIST
	     (LET ((DEFAULT-CONS-AREA SI:BACKGROUND-CONS-AREA))
	       (COND ((BOUNDP 'UCADR-STATE-LIST) UCADR-STATE-LIST)
		     (T (SETQ UCADR-STATE-LIST (GET-UCADR-STATE-LIST))))))
	   (MLIST
	     (GET (LOCF SLIST) 'MC-LINKAGE-ALIST)))
      ;;Note. Things are pushed onto forms in the logical order. Forms are then
      ;; reversed, so that things will happen in that order at run time, and
      ;;  divided into several functions, to avoid FEF-too-large lossage.
      (CONS-LAP SOURCE SLIST)
      (DOLIST (RANGE A-MEMORY-RANGE-LIST)
        (DOTIMES (I (CADR RANGE))
          (LET ((ADDRESS (+ I (CAR RANGE))))
            (PUSH `(MA-LOAD-A-MEM ,ADDRESS ,(#-symbolics AREF A-MEM ADDRESS))
                  FORMS))))
      (DOLIST (RANGE D-MEMORY-RANGE-LIST)
        (DOTIMES (I (CADR RANGE))
          (LET ((ADDRESS (+ I (CAR RANGE))))
            (PUSH `(MA-LOAD-D-MEM ,ADDRESS ,(#-symbolics AREF D-MEM ADDRESS))
                  FORMS))))
      (DOLIST (RANGE I-MEMORY-RANGE-LIST)
        (DOTIMES (I (CADR RANGE))
          (LET ((ADDRESS (+ I (CAR RANGE))))
            (PUSH `(MA-LOAD-I-MEM ,ADDRESS ,(#-symbolics AREF I-MEM ADDRESS))
                  FORMS))))
      (MAPC #'(LAMBDA (X)
		(LET* ((SYMBOL-INDEX (- (GET (CADR X) 'QLVAL) 200))
		       (XP (INTERN (STRING (CADR X)) "PROLOG")))
		  (COND ((OR (GET XP 'COMPILER:QINTCMP)
			     (MEMQ '&REST (ARGLIST XP)))
			 (PUSH `(PUSH (CONS ',XP ',SYMBOL-INDEX)
				      COMPILER:*MA-MICRO-CODE-SYMBOL-INDEX-ASSIGNMENTS*)
			       FORMS)))
		  (PUSH `(COMPILER:MA-INSTALL
			   ',XP
			   ',(GET XP 'ARGS-INFO)
			   (GET ',XP 'COMPILER:ARGLIST)
			   ',(CADDR X))
			FORMS)
		  (PUSH `(SETF (SYS:MICRO-CODE-SYMBOL-NAME-AREA
				 (COMPILER:GET-MICRO-CODE-SYMBOL-INDEX ',XP))
			       ',XP)
			FORMS)))
            CURRENT-ASSEMBLY-MICRO-ENTRIES)
      `(PROGN 'COMPILE
	      (eval-when (compile eval load)
		;;Initialize dynamic loader to include our frobs.
		(defconst INCREMENTAL-ASSEMBLY-MC-LINKAGE-ALIST
			  ',(MAPCAR #'(LAMBDA (ITEM)
					`(,(INTERN (STRING (CAR ITEM)) "COMPILER")
					  ,(INTERN (STRING (CADR ITEM)) "COMPILER")
					  ,(CADDR ITEM)))
				    (LDIFF MC-LINKAGE-ALIST MLIST)))
		(COMPILER:MA-LOAD)
		(SETQ COMPILER:*A-CONSTANT-TABLE-OFFSET* ',A-CONSTANT-LOC
		      COMPILER:*C-MEM-LOC* ',I-MEM-LOC
		      COMPILER:*MC-LINKAGE-ALIST*
		      (APPEND INCREMENTAL-ASSEMBLY-MC-LINKAGE-ALIST
			      COMPILER:(GET (LOCF *UCADR-STATE-LIST*) 'MC-LINKAGE-ALIST))))
              ,@(MAPCAR #'(LAMBDA (NAME GROUP)
                            `(DEFUN ,NAME ()
                               (LET ((SYS:%INHIBIT-READ-ONLY T)) ,@GROUP)))
                        NAMES
                        (NREVERSE
                          (FORM-GROUPS FORMS 0
                                       (1+ (// (LENGTH FORMS) (LENGTH NAMES)))
                                       ())))))))

(DEFMACRO MA-LOAD-I-MEM (ADR I)
  `(SI:%WRITE-INTERNAL-PROCESSOR-MEMORIES 1 ',ADR
    ',(%LOGDPB (LDB 4020 I) 1020 (LDB 3010 I))  ;Assure no bignums
    ',(%LOGDPB (LDB 1020 I) 1020 (LDB 0010 I))))

(DEFMACRO MA-LOAD-A-MEM (ADR A)
  `(SI:%WRITE-INTERNAL-PROCESSOR-MEMORIES 4 ',ADR    ;A/M
    ',(%LOGDPB (LDB 4020 A) 1020 (LDB 3010 A))
    ',(%LOGDPB (LDB 1020 A) 1020 (LDB 0010 A))))

(DEFMACRO MA-LOAD-D-MEM (ADR V)
  ;;Courtesy UA:CONS-LAP-PASS2, UA:WRITE-D-MEM
    `(SI:%WRITE-INTERNAL-PROCESSOR-MEMORIES
       2 ',ADR    ;2 for D-MEM
       0               ;Never any high bits
       ',(DPB (DO ((COUNT 17. (1- COUNT)) ;Adding odd parity bit
                   (X V (LOGXOR V (LSH X -1))))
                  ((= COUNT 0)
                   (LOGXOR 1 X)))
              2101
              V)))

(DEFMACRO MODIFY-DISPATCH-TABLE (CC:LABEL OFFSET WORD)
  (LET* ((LOCALITY 'D-MEM)
	 (D-MEM-LOC
	   (COND ((LISTP CC:LABEL)
		  (+ OFFSET (LDB 1416 (CONS-WORD-EVAL (LIST CC:LABEL)))))
		 (T (+ OFFSET (LDB 0014 CC:(CC-LOOKUP-NAME LABEL))))))
	 (INSN (CONS-WORD-EVAL WORD)))
    `(MA-LOAD-D-MEM ,D-MEM-LOC
		    ,(+ (LSH (LDB 703 INSN) 14.)  ;RPN bits from jump
			(LDB 1416 INSN)))))

(defun /#/_-reader (ignore stream)
  (pkg-bind "CC"
    (let ((thing (read stream)))
      (let-if si:read-area ((default-cons-area si:read-area))
	(cond ((atom thing) `(eval (cc:cc-linkage ',thing)))
	      ((eq (car thing) 'cc:i-mem-loc)
	       (ldb #+cadr 0016 #-cadr 0020 (cc:cc-lookup-name (cadr thing))))
	      (t (cerror nil nil ':syntax "~%Bad /#/_ syntax: ~S" thing)))))))

(READFILE "LMP:KERNEL;DEFMIC-PROLOG" "UA" T)
(READFILE "LMP:KERNEL;UC-PROLOG" "UA" T)
)
