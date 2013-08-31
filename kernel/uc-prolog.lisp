;; -*- Mode: Lisp; Base: 8. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;; Incremental microcode for LM-Prolog for CADR/LM-2.
;;; Potentially dangerous POPJs are marked with ***,
;;; since they could start a macro insn cycle.  However, the corresponding MISCs
;;; are pretty useless with D-IGNORE.

;;; Wired in assumptions on storage conventions:
;;; >> Fill-pointers are at offset -2 from the array pointer.
;;; >> Flavor instances look like <header word, instance vas...>

(defconst uc-prolog '(  
  (mc-linkage (;;a-mem communication frobs
	       a-unify-dispatch
	       a-lmp-vector
	       a-lmp-trail
	       a-lmp-area
	       a-lmp-mode
	       ;;the following are used for modifying dispatch tables
	       #-Commonlisp LMP-SEND-CAR
	       #-Commonlisp LMP-SEND-CDR
	       LMP-NODEST
	       LMP-NODEST-NOSOURCE
	       ;;the following are needed because of LAST-ARG-IN-T properties 
	       lmp-cell
	       lmp-reference
	       lmp-dereference
	       lmp-updl
	       lmp-centry
	       lmp-invoke
	       ;;the following are needed for our unify-dispatch-table
	       lmp-pop-fail
	       lmpu-x-x
	       lmpu-instance-x
	       lmpu-x-instance
	       lmpu-var-x
	       lmpu-x-var
	       lmpu-var-var
	       lmpu-var-list
	       lmpu-list-var
	       lmpu-list-list
	       ))

;;Exit vector offsets.
    (assign lmpoff-unify 765)
    (assign lmpoff-occurs-in 766)
    (assign lmpoff-unify-term-with-template 767)
    (assign lmpoff-construct 770)
    (assign lmpoff-unify-term-with-term 771)
    (assign lmpoff-array-push-extend 772)
    (assign lmpoff-read-only-variable-flavor 773)
    (assign lmpoff-true 774)
    (assign lmpoff-false 775)
    (assign lmpoff-find-and-cache 776)
    (assign lmpoff-universe 777)

;;Use a bit to distinguish variables (locatives) from conses. Not essential.
    (def-data-field lmp-data-type-low-bit 1 #.%%q-pointer)
    (def-data-field boxed-sign-bit 1 #.(1- %%q-pointer))

    (DEF-DATA-FIELD Q-TYPED-POINTER #.%%q-typed-pointer 0)
    (DEF-DATA-FIELD Q-DATA-TYPE-PLUS-ONE-BIT 6 #.(1- %%q-pointer))
    (DEF-DATA-FIELD Q-DATA-TYPE 5 #.%%q-pointer)
    (DEF-DATA-FIELD Q-POINTER #.%%q-pointer 0)
    (DEF-DATA-FIELD Q-CDR-CODE 2 36)
    (ASSIGN TRANSPORT (PLUS (I-ARG #+symbolics 41 #-symbolics 1)
			    Q-DATA-TYPE-PLUS-ONE-BIT DISPATCH-ON-MAP-19
                            DISPATCH-PUSH-OWN-ADDRESS #_D-TRANSPORT))
    (ASSIGN TRANSPORT-HEADER (PLUS (I-ARG #+symbolics 44 #-symbolics 4)
				   Q-DATA-TYPE-PLUS-ONE-BIT DISPATCH-ON-MAP-19
				   DISPATCH-PUSH-OWN-ADDRESS #_D-TRANSPORT))
    (ASSIGN CHECK-PAGE-READ (PLUS CALL-CONDITIONAL PG-FAULT-OR-INTERRUPT #_PGF-R-I))
    (ASSIGN CHECK-PAGE-WRITE (PLUS CALL-CONDITIONAL PG-FAULT-OR-INTERRUPT #_PGF-W-I))
    (ASSIGN PG-FAULT-OR-INTERRUPT JUMP-ON-PAGE-FAULT-OR-INTERRUPT-PENDING-CONDITION)


    (DEF-BIT-FIELD-IN-REG M-INST-REGISTER 3 6 (PLUS M-INST-BUFFER INSTRUCTION-STREAM))

    (DEF-BIT-FIELD-IN-REG M-INST-ADR 11 0 (PLUS M-INST-BUFFER INSTRUCTION-STREAM))
  
    (DEF-BIT-FIELD-IN-REG M-INST-DEST-3 3 15 (PLUS M-INST-BUFFER INSTRUCTION-STREAM))

    (DEF-BIT-FIELD-IN-REG M-INST-DEST-2 2 #-Commonlisp 15 #+Commonlisp 16
			  (PLUS M-INST-BUFFER INSTRUCTION-STREAM))

    (DEF-DATA-FIELD OAL-JUMP 14. 12.)


        (locality d-mem)
;;Tail-recursive calls.
        (start-dispatch 0 0)
d-lmp-mmjcall
	(#_mmjcall inhibit-xct-next-bit)		;tail recursive call
        (end-dispatch)

;;%UNIFY-TERM-WITH-TEMPLATE
        (start-dispatch 3 0)			;PPSS 2503: what kind of occurrence.
d-lmp-unify
        (lmp-put-frame inhibit-xct-next-bit)	;first occurrence
        (lmp-updl)				;subsequent occurrence
	(lmp-pop-succeed inhibit-xct-next-bit)	;void occurrence
	(#_illop inhibit-xct-next-bit)
        (lmp-ro-unify-1 inhibit-xct-next-bit)	; read-only first occurrence
        (lmp-ro-unify-2)			; read-only subsequent occurrence
	(lmp-ro-uvoid inhibit-xct-next-bit)	; read-only void occurrence
	(#_illop inhibit-xct-next-bit)
        (end-dispatch)

;;%CONSTRUCT
        (start-dispatch 3 0)			;PPSS 2503: what kind of occurrence.
d-lmp-construct
        (lmp-put-cell-frame inhibit-xct-next-bit) 	;first occurrence
        (lmp-get-frame inhibit-xct-next-bit)      	;subsequent occurrence
	(lmp-cell inhibit-xct-next-bit)			;void occurrence
	(#_illop inhibit-xct-next-bit)
        (lmp-ro-construct-1 inhibit-xct-next-bit) 	; read-only first occurrence
        (lmp-ro-construct-2 inhibit-xct-next-bit) 	; read-only subsequent occurrence
	(lmp-ro-construct-void inhibit-xct-next-bit) 	; read-only void occurrence
	(#_illop inhibit-xct-next-bit)
        (end-dispatch)

;;First occurrences.
        (start-dispatch 2 0)			;PPSS 2302: base reg ;PPSS 0023: offset
d-lmp-put-frame
        (lmp-put-vector)			;interpreter's vector
        (#_qstarg)				;argument block
        (#_qstloc)				;local block
        (lmp-xstore)				;higher context.
        (end-dispatch)

;;Subsequent occurrences.
        (start-dispatch 2 0)			;PPSS 2302: base reg ;PPSS 0023: offset
d-lmp-get-frame
        (lmp-get-vector)			;interpreter's vector
        (#_qadarg1)				;argument block
        (#_qadloc1)				;local block
        (lmp-xload)				;higher context.
        (end-dispatch)

;;Special va:s in A-MEM.
        (locality a-mem)
a-unify-dispatch (0)
a-lmp-vector (0)
a-lmp-trail (0)
a-lmp-area (0)
a-lmp-mode (0)

;;And now for the actual code.
        (locality i-mem)

#+CommonLisp (begin-comment)

;; Glorious message passing customization of CAR and CDR. Done by LMI in recent systems.
;; N.B. Can get here from %spread, who expects M-A M-B M-C to still be valid,
;;      and from CAR CDR C..R instructions, who need M-INST-BUFFER later.
;; %SPREAD uses typed M-A, untyped M-B, untyped M-C.
;; APPLY additionally uses untyped M-R (M-S?) but does a CONSP test and so is
;;out of the question???


	(assign lmpoff-car 763)
	(assign lmpoff-cdr 764)
	(def-data-field q-low 20 0)
	(def-data-field q-high 20 20)
	
LMP-SEND-CAR
	(jump-xct-next lmp-send1)
       (dispatch-call (i-arg lmpoff-car) #_d-read-exit-vector)
LMP-SEND-CDR
	(dispatch-call (i-arg lmpoff-cdr) #_d-read-exit-vector)
lmp-send1
	(call-xct-next lmp-push-both-halves)
       ((m-1) m-a)
	(call-xct-next lmp-push-both-halves)
       ((m-1) m-b)
	(call-xct-next lmp-push-both-halves)
       ((m-1) m-c)
	(call-xct-next lmp-push-both-halves)
       ((m-1) m-inst-buffer)
	(call #_p3zero)
	((pdl-push) m-t)
	((pdl-push) q-typed-pointer md (a-constant (byte-value q-cdr-code cdr-nil)))
	(dispatch-call (i-arg 1) #_d-mmcall)
	(call lmp-pop-both-halves)
	((m-inst-buffer) m-1)
	(call lmp-pop-both-halves)
	((m-c) m-1)
	(call lmp-pop-both-halves)
	((m-b) m-1)
	(call lmp-pop-both-halves)
	((m-a) m-1)
	(popj)
lmp-push-both-halves
	(popj-after-next
	  (pdl-push) q-high m-1 (a-constant (byte-value q-data-type dtp-fix)))	;high half
       ((pdl-push) q-low m-1 (a-constant (byte-value q-data-type dtp-fix)))	;low half
lmp-pop-both-halves
	(popj-after-next (m-1) pdl-pop)		;low half
       ((m-1) dpb pdl-pop q-high a-1)		;high half

#+CommonLisp (end-comment)

;;; Prolog-specific instructions.

	(locality d-mem)
	(start-dispatch 3 0)
d-lmp-nodest
	(lmp-reference)
	(lmp-dereference)
	(lmp-cell-named)
	(lmp-updl)
	(lmp-nodest-utemplate)
	(lmp-centry)
	(lmp-invoke)
	(lmp-nodest-untrail)
	(end-dispatch)

	(start-dispatch 2 0)
d-lmp-nodest-nosource
	(lmp-prolog-list)
	(lmp-prolog-list*)
	(lmp-cell0)
	(#_illop)
	(end-dispatch)

	(locality i-mem)
lmp-nodest
        (dispatch-call m-inst-register #_qadcm5)
	(dispatch-xct-next m-inst-dest-3 d-lmp-nodest)
       ((micro-stack-data-push) (a-constant #_(i-mem-loc m-t-to-stack)))

lmp-nodest-utemplate				;Wants arg in K.
	(jump-xct-next lmp-utemplate-k)
       ((m-k) m-t)

lmp-nodest-untrail				;Wants clean arg on PDL.
	(jump-xct-next lmp-untrail-restart)
       ((pdl-push) q-typed-pointer m-t)

lmp-nodest-nosource
	((m-r) m-inst-adr)
	(dispatch-xct-next m-inst-dest-2 d-lmp-nodest-nosource)
       ((micro-stack-data-push) (a-constant #_(i-mem-loc m-t-to-stack)))

	 (misc-inst-entry occurs-in)
  	 ((m-a) q-typed-pointer pdl-pop)
	 ((m-k) q-typed-pointer pdl-pop)

lmp-occurs-in
        (dispatch q-data-type m-a #_skip-if-list)
         (jump lmp-occurs-in-atom)

lmp-occurs-in-list
	(call-xct-next lmp-carcdr)
       ((m-t) m-a)
        (dispatch q-data-type m-a #_skip-if-list)
         (jump-xct-next lmp-occurs-in-simple-recurse)
	((pdl-push) m-t)
	 (jump-greater-than micro-stack-pntr-and-data (a-constant 20._24.)
			    lmp-occurs-in-slow-recurse)	;Ustack filling up?
	 (jump-xct-next lmp-occurs-in-join)	;No, proceed. (Should check stack frame too.)
	(call lmp-occurs-in-list)

lmp-occurs-in-atom
	 ((m-t) #_a-v-nil)
	 (popj-after-next popj-not-equal m-k a-a)
	((m-t) #_a-v-true)

lmp-occurs-in-simple-recurse
	 (call lmp-occurs-in-atom)

lmp-occurs-in-join				;Here with key in K and term on stack
	 ((m-a) q-typed-pointer pdl-pop)
	 (popj-not-equal m-t #_a-v-nil)
	 (jump lmp-occurs-in)

lmp-occurs-in-slow-recurse
	 ((pdl-push) m-k)
	 (dispatch-call (i-arg lmpoff-occurs-in) #_d-call-exit-vector)
	 ((pdl-push) q-typed-pointer m-k (a-constant (byte-value q-cdr-code cdr-next)))
	 ((pdl-push) q-typed-pointer m-a (a-constant (byte-value q-cdr-code cdr-nil)))
	 (dispatch-call (i-arg 2) #_d-mmcall)
	 (jump-xct-next lmp-occurs-in-join)
	((m-k) q-typed-pointer pdl-pop)

	(misc-inst-entry %reference)
        ((m-t) q-typed-pointer pdl-pop)

lmp-reference					;Inviz. T if it is a variable.
        ((m-1) q-data-type m-t)
        (popj-after-next popj-not-equal m-1 (a-constant (eval dtp-locative)))
       ((m-t) q-pointer m-t
	(a-constant (byte-value q-data-type dtp-external-value-cell-pointer)))

	(misc-inst-entry %dereference)
        ((m-t) q-typed-pointer pdl-pop)

lmp-dereference					;Read T if it is a variable.
        ((m-1) q-data-type m-t)
        (popj-not-equal m-1 (a-constant (eval dtp-locative)))
	((vma-start-read) m-t)
	(check-page-read)
	(popj-after-next dispatch transport md)
       ((m-t) q-typed-pointer md)

;;; *** Callers depend on A being preserved by %CELL and %CELL0. ***

lmp-cell
	(jump-not-equal m-t #_a-v-nil lmp-cell-named)
	(misc-inst-entry %cell0)		;Make an unnamed value cell.

lmp-cell0
        ((m-b) (a-constant 1))			;Cons 1 word
        (call-xct-next #_lcons)
       ((m-s) a-lmp-area)			;in *PROLOG-WORK-AREA*
        ((m-t vma) q-pointer m-t (a-constant (byte-value q-data-type dtp-locative)))
        (popj-after-next (md-start-write)	;***
         q-typed-pointer m-t (a-constant (byte-value q-cdr-code cdr-nil)))
        (check-page-write)			;Store a self-reference.
        ;(gc-write-test)

lmp-cell-named
	((pdl-push) m-t)
	(misc-inst-entry %cell)			;Make a named value cell.
        ((m-b) (a-constant 2))			;Cons 2 words
        (call-xct-next #_lcons)
       ((m-s) a-lmp-area)			;in *PROLOG-WORK-AREA*
        ((m-t vma) q-pointer m-t (a-constant (byte-value q-data-type dtp-locative)))
        ((md-start-write) q-typed-pointer m-t (a-constant (byte-value q-cdr-code cdr-normal)))
        (check-page-write)			;Store a self-reference.
        ;(gc-write-test)
        ((vma) m+1 vma)
        (popj-after-next			;***
	  (md-start-write)
	  q-typed-pointer pdl-pop (a-constant (byte-value q-cdr-code cdr-error)))
        (check-page-write)			;Store the name.
        ;(gc-write-test)

        (misc-inst-entry %prolog-list)
        ((m-r) q-pointer pdl-pop)		;number of elements
lmp-prolog-list
        (jump-equal m-r a-zero #_xfalse)

lmp-list
	((m-b) m-r)				;Cons R words
        ((m-s) a-lmp-area)			;in *PROLOG-WORK-AREA*
        (jump-xct-next #_xlist0)
       (call #_lcons)

        (misc-inst-entry %prolog-list*)
        ((m-r) q-pointer pdl-pop)		;number of elements
lmp-prolog-list*
        (jump-equal m-r (a-constant 1) #_poptj)

lmp-list*
	((m-b) m-r)				;Cons R words
        ((m-s) a-lmp-area)			;in *PROLOG-WORK-AREA*
        (jump-xct-next #_xlistr0)
       (call #_lcons)

        (misc-inst-entry %unify-term-with-template)

lmp-utemplate
        ((m-k) q-typed-pointer pdl-pop)
lmp-utemplate-k
        (call-if-bit-set-xct-next lmp-data-type-low-bit pdl-top lmp-dereference)
       ((m-t) q-typed-pointer pdl-pop)
	((pdl-push) m-t)
	(jump-equal m-k #_a-v-nil lmp-unil)

lmp-utemplate-nd				;Here if don't need to dereference
						;Template in M-K  NIL.
        ((m-1) q-data-type m-k)
        (jump-equal m-1 (A-CONSTANT (EVAL DTP-LIST)) lmp-uconstruct)
        (jump-equal m-1 (A-CONSTANT (EVAL DTP-LOCATIVE)) lmp-uconstant)
        (call-equal-xct-next m-1 (A-CONSTANT (EVAL DTP-SYMBOL)) lmp-symeval-a)
       ((m-a) m-k)
	(dispatch (byte-field 3 25) m-a d-lmp-unify)	;XCT-NEXT only if subsequent occ.
       (call lmp-get-frame-d)

lmp-uconstant
	((m-t) m-k)
	(jump-xct-next lmp-updl)
       (call #_qcar3)

lmp-symeval-a
	((vma-start-read) m+1 m-a)
	(check-page-read)
	(dispatch transport md)
        (popj-after-next (m-t) m-a)
       ((m-a) q-typed-pointer md)

lmp-uconstruct					;X & construct
        ((m-t) m-k)
        (dispatch q-data-type pdl-top #_skip-if-list)
         (jump lmp-uconstruct-1)
	(call lmp-carcdr)			;List & construct.
        ((m-k) m-a)				;Recurse, pushing cdrs.
        ((m-c) m-t)
	(call-xct-next lmp-carcdr)
       ((m-t) q-typed-pointer pdl-pop)
        ((pdl-push) m-t)
        ((pdl-push) m-c)
        (jump-equal-xct-next m-k #_a-v-nil lmp-unil-then-join)
       ((pdl-push) m-a)
	(call-greater-than
	  micro-stack-pntr-and-data (a-constant 20._24.)	;(Should check frame too.)
	  lmp-utemplate-slow-recurse)
	(call-less-or-equal
	  micro-stack-pntr-and-data (a-constant 20._24.)	
	  lmp-utemplate-nd)
lmp-uconstruct-join
	(jump-not-equal m-t #_a-v-nil lmp-utemplate)
	;drop thru and fail otherwise

lmp-pop2-fail					;Pop two and fail.
	(popj-after-next (m-t) seta pdl-pop #_a-v-nil)
       (pdl-pop)

lmp-utemplate-slow-recurse			;MMcall %unify-term-with-template.
        (dispatch-call PDL-POP (i-arg lmpoff-unify-term-with-template) #_d-call-exit-vector)
        ((pdl-push) q-typed-pointer m-a (a-constant (byte-value q-cdr-code cdr-next)))
        ((pdl-push) q-typed-pointer m-k (a-constant (byte-value q-cdr-code cdr-nil)))
        (dispatch (i-arg 2) d-lmp-mmjcall)

lmp-uconstruct-1				;Atom & construct.
        ((m-1) q-data-type pdl-top)
        (jump-not-equal m-1 (a-constant (eval dtp-locative)) lmp-uconstruct-2)
	;Variable & complex term.  Construct it and bind.
        (call lmp-construct-t)
	(jump-xct-next lmpu-var-list)
       ((m-i) a-lmp-mode)

lmp-uconstruct-2
        (jump-not-equal m-1 (a-constant (eval dtp-instance)) lmp-pop-fail)
	;Instance & complex term.  Construct it and send :unify msg.
        (jump-xct-next lmpu-instance-x)
       (call lmp-construct-t)

	(misc-inst-entry %construct)
        ((m-t) q-typed-pointer pdl-pop)
	(popj-equal m-t #_a-v-nil)
lmp-construct-t
        ((m-1) q-data-type m-t)
        (jump-equal m-1 (a-constant (eval dtp-list)) lmp-construct-list)
lmp-construct-not-list
        (jump-equal m-1 (a-constant (eval dtp-locative)) #_qcar3)
	((m-a) m-t)
        (call-equal-xct-next m-1 (a-constant (eval dtp-symbol)) lmp-symeval-a)
       ((m-t) #_a-v-nil)
        (dispatch (byte-field 3 25) m-a d-lmp-construct)

lmp-construct-list				;Construct the cons sitting in T.
	(jump-greater-than micro-stack-pntr-and-data (a-constant 20._24.)
			   lmp-construct-slow-recurse)	;Chicken out?
	(call-xct-next lmp-construct-list-rest)
       ((pdl-push) (a-constant (byte-value q-data-type dtp-fix)))	;Push count first.
        (jump-equal-xct-next m-t #_a-v-nil lmp-list)	;LIST* the elements.
       ((m-r) q-pointer pdl-pop)		;R long.
	;invz last element if need be
        (call-if-bit-set lmp-data-type-low-bit m-t lmp-reference)
        ((pdl-push) m-t)
        (jump-xct-next lmp-list*)
       ((m-r) m+1 m-r)

lmp-construct-list-rest
	(call lmp-carcdr)
        ((pdl-push) m-t)
	(jump-equal-xct-next m-a #_a-v-nil lmp-construct-list-cdr)
       ((m-t) m-a)
	(call lmp-construct-t)
	;invz element if need be
        (call-if-bit-set lmp-data-type-low-bit m-t lmp-reference)
lmp-construct-list-cdr
        ((m-k) q-typed-pointer pdl-pop)		;pop rest of template
        ((m-s) q-typed-pointer pdl-pop)		;pop count
        ((pdl-push) m-t)			;push element
	((pdl-push) m+1 m-s)			;push incf count
	(popj-equal-xct-next m-k #_a-v-nil)
       ((m-t) m-k)
        ((m-1) q-data-type m-t)
        (jump-not-equal m-1 (a-constant (eval dtp-list)) lmp-construct-not-list)
	((pdl-buffer-index) sub pdl-buffer-pointer a-ap)	;Stack frame filling up?
        (jump-less-or-equal pdl-buffer-index (a-constant 370) lmp-construct-list-rest)
	;drop thru if frame is filling up

lmp-construct-slow-recurse
	((m-k) m-t)				;CALL-EXIT-VECTOR clobbers M-T...
        (dispatch-call (i-arg lmpoff-construct) #_d-call-exit-vector)
        ((pdl-push) q-typed-pointer m-k (a-constant (byte-value q-cdr-code cdr-nil)))
        (dispatch (i-arg 1) d-lmp-mmjcall)

lmp-put-frame					;Store PDL-POP in local frame and succeed.
        ((m-t) q-typed-pointer pdl-top)
	((micro-stack-data-push) (a-constant (i-mem-loc lmp-pop-succeed)))
        (dispatch-xct-next (byte-field 2 23) m-a d-lmp-put-frame)
       ((m-1) (byte-field 23 0) m-a)

lmp-put-cell-frame				;Store a cell into local frame and return it.
        (call lmp-cell)
        (dispatch-xct-next (byte-field 2 23) m-a d-lmp-put-frame)
       ((m-1) (byte-field 23 0) m-a)

lmp-get-frame-d					;Dereference after doing...
	((micro-stack-data-push) (a-constant (i-mem-loc lmp-dereference)))
lmp-get-frame					;Get from local frame into T
        (dispatch-xct-next (byte-field 2 23) m-a d-lmp-get-frame)
       ((m-1) (byte-field 23 0) m-a)

lmp-put-vector					;Store in interpreter's vector.
	(call-xct-next #_qrar3)
       ((m-s) add m-1 a-lmp-vector)
	(popj-after-next (m-t) q-typed-pointer md)
       (no-op)

lmp-get-vector					;Read from interpreter's vector.
        (jump-xct-next #_qcar3)
       ((m-t) add m-1 a-lmp-vector)

lmp-ro-construct-void				;Make read-only void.
	(jump-xct-next lmp-ro-allocate)
       (call lmp-cell)

lmp-ro-construct-1				;Make read-only 1st occ.
	(jump-xct-next lmp-ro-allocate)
       (call lmp-put-cell-frame)

lmp-ro-construct-2				;Make read-only 2nd occ.
	(call lmp-get-frame-d)
        ((m-2) q-data-type m-t)
        (popj-not-equal m-2 (a-constant (eval dtp-locative)))

;;(make-instance-in-area *prolog-work-area* read-only-variable ':cell <T>)
lmp-ro-allocate
	((pdl-push) m-t)
        ((m-b) (a-constant 2))			;Cons 2 words
        (call-xct-next #_scons)
       ((m-s) a-lmp-area)			;in *PROLOG-WORK-AREA*
	(dispatch-call (i-arg lmpoff-read-only-variable-flavor) #_d-read-exit-vector)
	((write-memory-data)
	 q-pointer md (a-constant (byte-value q-data-type dtp-instance-header)))
	((vma-start-write m-t)
	 q-pointer m-t (a-constant (byte-value q-data-type dtp-instance)))
        (check-page-write)
	((md) q-typed-pointer pdl-pop (a-constant (byte-value q-cdr-code cdr-nil)))
	(popj-after-next			;***
	  (vma-start-write) add m-t (a-constant 1))
       (check-page-write)

lmp-ro-uvoid					;Unify with read-only void.
        ((m-1) q-data-type pdl-top)		;Term must be a variable.
        (jump-not-equal m-1 (a-constant (eval dtp-locative)) lmp-pop-fail)
	(jump-xct-next lmpu-var-x)
       (call lmp-ro-construct-void)

lmp-ro-unify-1					;Unify with read-only 1st occ.
        ((m-1) q-data-type pdl-top)		;Term must be a variable.
        (jump-not-equal m-1 (a-constant (eval dtp-locative)) lmp-pop-fail)
	(jump-xct-next lmpu-var-x)
       (call lmp-ro-construct-1)

lmp-ro-unify-2					;Unify with read-only 2nd occ.
        ((m-1) q-data-type pdl-top)
        (jump-not-equal-xct-next m-1 (a-constant (eval dtp-locative)) lmp-ro-unify-nonvar)
       ((m-2) q-data-type m-t)			;V&V  bind to read-only instance, V&NV  bind
        (jump-xct-next lmpu-var-x)
       (call-equal m-2 (a-constant (eval dtp-locative)) lmp-ro-allocate)

lmp-ro-unify-nonvar				;NV&V  fail, NV&NV  unify
        (jump-not-equal m-2 (a-constant (eval dtp-locative)) lmp-updl)
	(jump lmp-pop-fail)


lmp-unil-then-join
	((micro-stack-data-push) (a-constant (i-mem-loc lmp-uconstruct-join)))
lmp-unil					;Unify PDL with NIL.
	((pdl-top m-tem) q-typed-pointer pdl-top)
	(jump-equal m-tem #_a-v-nil lmp-pop-succeed)
        ((m-1) q-data-type pdl-top)
        (jump-equal-xct-next m-1 (a-constant (eval dtp-locative)) lmpu-var-x)
       ((m-t) #_a-v-nil)
        (jump-equal m-1 (a-constant (eval dtp-instance)) lmpu-instance-x)
	;All other cases fail...

lmp-pop-fail					;Pop one and fail.
	(popj-after-next (m-t) #_a-v-nil)
       (pdl-pop)



        (misc-inst-entry %unify-term-with-term)
        ((m-t) q-typed-pointer pdl-pop)

lmp-updl					;Here to unify PDL with T.
	((m-s pdl-top) q-typed-pointer pdl-top)	;Make S=PDL
	(jump-equal m-s a-t lmp-pop-succeed)

;General unification.  Dispatch on two datatypes via a main mem. table of ucode pcs.
;M-I has A-LMP-MODE, +BOXED-SIGN-BIT if it's the first time. 

	((m-i) dpb m-minus-one boxed-sign-bit a-lmp-mode)

lmp-updl-1					;Unify S=PDL with T and ST.
        ((m-3) ldb (byte-field 10. (eval (- %%q-pointer 5.))) m-s a-zero)
	((m-3) ldb q-data-type m-t a-3)
	((vma-start-read) add m-3 a-unify-dispatch)
	(check-page-read)			;no transport since it's static
	((oa-reg-low) dpb md oal-jump a-zero)
        (jump-xct-next 0)
       ((m-c) m-s)				;for  LMPU-LIST-LIST.

lmpu-x-x					;Chicken out to EQUAL.
	((pdl-push) m-t)
	(jump #_xequal)

lmpu-var-var					;Variable & variable.
	(jump-xct-next lmpu-var-x)
       ((m-t) q-pointer m-t
	(a-constant (byte-value q-data-type dtp-external-value-cell-pointer)))

lmpu-list-var					;List & variable.
	((pdl-top) m-t)
	((m-t) m-s)
	;drop thru

lmpu-var-list					;Variable & list.
	(call-if-bit-set (byte-field 1 0) m-i lmpu-var-list-check)
	;drop thru

lmpu-var-x					;Variable & anything.
	(call-xct-next #_qrar3)
       ((m-s) q-typed-pointer pdl-pop)
	;Now trail the clobbered cell.
        (call lmp-gahd)
        ((vma-start-read) sub m-a (a-constant 2))
	(check-page-read)
	((m-q) q-pointer md)
	(jump-greater-or-equal-xct-next	   ;Check overflow.
	  m-q a-s lmpu-var-x-overflow)
       ((m-k) m-t)
	((m-t md-start-write) m+1 md)	   ;Bump fill-pointer.
	(check-page-write)
	((vma) add m-e a-q)
	((md-start-write) m-k)		   ;Store trail-item.
	(check-page-write)
	(popj)

lmpu-var-x-overflow			   ;The trail has overflown.  Grow it.
        (dispatch-call (i-arg lmpoff-array-push-extend) #_d-call-exit-vector)
        ((pdl-push) a-lmp-trail)		;Don't worry about cdr code...
        ((pdl-push) q-typed-pointer m-k (a-constant (byte-value q-cdr-code cdr-nil)))
        (dispatch (i-arg 2) d-lmp-mmjcall)

lmpu-x-var					;Non-variable & variable.
	((pdl-top) m-t)
	(jump-xct-next lmpu-var-x)
       ((m-t) m-s)

lmpu-x-instance					;Non-variable & instance.
	((pdl-top) m-t)
	((m-t) m-s)
	;drop thru

lmpu-instance-x					;Instance & non-variable.
        (call-xct-next #_p3zero)		;Escape to a :UNIFY method.
       ((m-s) q-typed-pointer pdl-pop)
        ((pdl-push) m-s)
        (dispatch-call (i-arg lmpoff-unify) #_d-read-exit-vector)
        ((pdl-push) q-typed-pointer md (a-constant (byte-value q-cdr-code cdr-next)))
        ((pdl-push) q-typed-pointer m-t (a-constant (byte-value q-cdr-code cdr-nil)))
        (dispatch (i-arg 2) d-lmp-mmjcall)

lmpu-list-list					;List & list.
	 (call-equal m-i (a-constant (plus (byte-value q-data-type dtp-fix) 6)) lmpu-unbind-later)
						;C already has first arg,
	 (call-xct-next lmp-carcdr)		;A and T get its parts.
	((m-d) m-t)				;D gets second arg,
	 ((m-b) m-a)				;B and S=TOP get its parts.
	 ((m-s pdl-top) m-t)
	 (call-xct-next lmp-carcdr)
	((m-t) m-c)
	 (jump-equal m-a a-b lmpu-equal-cars)
	 (jump-equal m-s a-t lmpu-equal-cdrs)
	 ((pdl-push) m-t)
	 ((pdl-push m-s) m-a)				;Recurse on cars.
	 (call-if-bit-set-xct-next (byte-field 1 1) m-i lmpu-llh-bind)
	((m-t) m-b)
	 (call-greater-than micro-stack-pntr-and-data (a-constant 20._24.)
		lmpu-slow-recurse)
	 (call-less-or-equal micro-stack-pntr-and-data (a-constant 20._24.)
		lmp-updl-1)
	 (jump-equal m-t #_a-v-nil lmp-pop2-fail)
	 ((pdl-buffer-index) sub pdl-buffer-pointer (a-constant 1))	;Dereference cdrs.
         (call-if-bit-set-xct-next lmp-data-type-low-bit c-pdl-buffer-index lmp-dereference)
        ((m-t) c-pdl-buffer-index)
         ((m-s c-pdl-buffer-index) m-t)
         (call-if-bit-set-xct-next lmp-data-type-low-bit pdl-top lmp-dereference)
        ((m-t) q-typed-pointer pdl-pop)
         (jump-not-equal-xct-next m-s a-t lmp-updl-1)	;Iterate on cdrs if neq.
	((m-i) a-lmp-mode)			        ;Ensure validity of M-I.
	 ;drop thru if cdrs eq.

lmp-pop-succeed
	 (popj-after-next (m-t) #_a-v-true)
	(pdl-pop)

lmpu-slow-recurse
	 ((m-a) pdl-pop)		   ;First arg pushed already.
	 ((m-b) m-t)
         (dispatch-call (i-arg lmpoff-unify-term-with-term) #_d-call-exit-vector)
         ((pdl-push) q-typed-pointer m-a (a-constant (byte-value q-cdr-code cdr-next)))
         ((pdl-push) q-typed-pointer m-b (a-constant (byte-value q-cdr-code cdr-nil)))
         (dispatch (i-arg 2) d-lmp-mmjcall)

lmpu-equal-cars				   ;Just iterate.
	 (jump-equal m-s a-t lmp-pop-succeed)
	 (jump-xct-next lmp-updl-1)
	(call-if-bit-set (byte-field 1 1) m-i lmpu-llh-bind)

lmpu-equal-cdrs				   ;Just iterate.
	 ((m-t) m-a)
	 ((pdl-top m-s) m-b)
	 (jump-xct-next lmp-updl-1)
	(call-if-bit-set (byte-field 1 1) m-i lmpu-llh-bind)

lmpu-var-list-check
	((m-k) pdl-top)
	(call-xct-next lmp-occurs-in-list)
       ((pdl-push m-a) m-t)
        (popj-equal-xct-next m-t #_a-v-nil)
       ((m-t) q-typed-pointer pdl-pop)
        (jump-xct-next lmp-pop-fail)	   ;Occur check succeeded, cause failure.
       (micro-stack-data-pop)

lmpu-llh-bind	;Bind the first cons to a HEADER-FORWARD to the second cons.
	 ((pdl-push) m-t)
         ((pdl-push) q-pointer m-c (a-constant (byte-value q-data-type dtp-locative)))
	 ((m-t) q-pointer m-d (a-constant (byte-value q-data-type dtp-header-forward)))
	 (jump-xct-next #_poptj)
        (call #_xbind1)

lmpu-unbind-later			   ;Save specPDL index and unwind before returning.
	 (popj-if-bit-clear boxed-sign-bit m-i)	;Popj if not first time.
	 ((m-3) #_a-qlbndp)
	 ((pdl-top) q-pointer m-3 (a-constant (byte-value q-data-type dtp-locative)))
	 ((pdl-push) m-s)
	 (popj-after-next (m-i) a-lmp-mode)	;Turn off boxed-sign-bit.
        ((micro-stack-data-push) (a-constant #_(i-mem-loc xunbind-to-index)))

lmp-carcdr					;A := car(T), T := cdr(T)
	  ((vma-start-read) m-t)
	  (check-page-read)
	  (dispatch transport md)
	  (jump-not-equal-xct-next vma a-t #_qcdr3)	;Full cdr if the car was forwarded
	 ((m-a) q-typed-pointer md)
	  (dispatch q-cdr-code md #_cdr-cdr-dispatch)	;XCT-NEXT on CDR-NEXT
	 ((m-t) add vma (a-constant 1))

        (misc-inst-entry %untrail)
;;Scratchpad registers used here:
;;PDL-TOP is MARK
;;M-I is transported array-pointer 
;;M-K is *TRAIL*
;;M-E is 1+last trail item address
        ((pdl-top) q-typed-pointer pdl-top)

lmp-untrail-restart				;Initialize.
        (call lmp-gahd)
	((vma-start-read) sub m-a (a-constant 2))
	(check-page-read)
        ((m-i) m-a)
        ((m-k) q-typed-pointer md)
        ((m-e) add m-e a-k)
	;drop in

lmp-untrail-loop
        (jump-greater-or-equal pdl-top a-k lmp-pop-fail)
        ((m-k md) sub m-k (a-constant 1))	;*TRAIL* := *TRAIL*-1
	((vma-start-write) sub m-i (a-constant 2))
	(check-page-write)
        ((m-e vma-start-read) sub m-e (a-constant 1))	;Get next item.
        (check-page-read)
	(dispatch transport md)			;Transport to newspace.
	((m-t) q-typed-pointer md)
	((md-start-write) #_a-v-nil)		;Clobber item with NIL.
	(check-page-write)
        ((m-1) q-data-type m-t)			;Unbind if we are a locative.
        (jump-not-equal m-1 (a-constant (eval dtp-locative)) lmp-untrail-invoke)
	((vma-start-read) m-t)
	(check-page-read)			;Transporting done already, just want the cdr code.
        ((md-start-write) selective-deposit md q-cdr-code a-t)
	(jump-xct-next lmp-untrail-loop)
       (check-page-write)

lmp-untrail-invoke
	(jump-xct-next lmp-untrail-restart)	;Re-initialize after invoking,
       (call lmp-invoke)			; since it can have side-effects.

	(misc-inst-entry %invoke)
;; This is as #-LEXICAL (apply (car x) (cdr x)) #+LEXICAL (funcall x),
;; but checks for TRUE and FALSE first, which are frequent cases in continuations.
	((m-t) q-typed-pointer pdl-pop)

lmp-invoke

	((m-i) a-lmp-mode)			;0201 iff lexical closures.
	(jump-if-bit-set (byte-field 1 2) m-i lmp-invoke-lexical)
        (dispatch q-data-type m-t #_skip-if-list)
	 (call #_illop)
	(call lmp-carcdr)		;A := fctn, T := args.
	(dispatch-call (i-arg lmpoff-true) #_d-read-exit-vector)
	((md) q-typed-pointer md)
	(jump-equal md a-a #_xtrue)		;Succeed if fctn is TRUE.
	(dispatch-call (i-arg lmpoff-false) #_d-read-exit-vector)
	((md) q-typed-pointer md)
	(popj-equal md a-a)			;Fail if fctn is FALSE.
	((pdl-push) m-a)
	(jump-xct-next #_uaply)			;APPLY otherwise.
      ((pdl-push) m-t)

lmp-invoke-lexical
	(CALL #_P3ZERO)
	((PDL-PUSH) M-T)
	(DISPATCH (I-ARG 0) D-LMP-MMJCALL)


	(misc-inst-entry %current-entrypoint)
	((m-t) q-typed-pointer pdl-pop)
lmp-centry
	((vma-start-read) m-t)			;K := definitions alist.
	(check-page-read)
	(dispatch transport md)
	((m-k) q-typed-pointer md)
        (dispatch-call (i-arg lmpoff-universe) #_d-read-exit-vector)	;B := *universe*.
	((m-b) q-typed-pointer md)
	(jump-equal m-k #_a-v-nil lmp-nodef)	;Any definitions at all?
	((vma-start-read) m-k)			;K := cache item.
	(check-page-read)
	(dispatch transport md)
	(call-xct-next lmp-carcdr)		;A := latest universe, T := defn.
       ((m-t) q-typed-pointer md)
        (jump-equal-xct-next m-b a-a #_qcar3)

lmp-nodef
       ((m-a) q-typed-pointer pdl-pop)		;A := predicator
	(dispatch-call (i-arg lmpoff-find-and-cache) #_d-call-exit-vector)
	((pdl-push) q-typed-pointer m-k (a-constant (byte-value q-cdr-code cdr-next)))	;defs
	((pdl-push) q-typed-pointer m-b (a-constant (byte-value q-cdr-code cdr-next)))	;worlds
	((pdl-push) q-typed-pointer m-a (a-constant (byte-value q-cdr-code cdr-nil)))	;name
	(jump-xct-next #_qcar)			;Full CAR since arg may become NIL.
       (dispatch-call (i-arg 3) #_d-mmcall)

;;Store in higher context.
 lmp-xstore
	 ((pdl-push) dpb m-zero (byte-field 5 23) a-a)
	 (jump #_xstore-in-higher-context)

;;Load from higher context.
 lmp-xload
	 ((pdl-push) dpb m-zero (byte-field 5 23) a-a)
	 (jump #_xload-from-higher-context)

;;; Get header of the trail array and assoc.  info.
;;; Courtesy GAHDR in UC-ARRAY, this is specialized code that does just what we want.

lmp-gahd
	((vma-start-read) a-lmp-trail)
	(check-page-read)
	(dispatch transport-header md)
	((m-a) q-pointer vma)			;M-A gets transported pointer.
	((m-e) m+1 m-a)				;M-E gets origin.
	(popj-after-next			;M-S gets size.
	  (m-s) (lisp-byte %%array-index-length-if-short) md)
       (call-if-bit-set (lisp-byte %%array-long-length-flag) md #_gahd3)
        ))
