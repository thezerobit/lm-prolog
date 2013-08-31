;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; Options:((WORLD CPROLOG) (DETERMINISTIC ALWAYS)); -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;this is the Concurrent Prolog interpreter written in LM-Prolog 
;;written 11/14/83 by E. Shapiro and Ken Kahn

;;Compiler written and graphics rewritten on 17 dec 1984 by Mats Carlsson.

;;; Read Only Variables.

(defmethod (read-only-variable :unify) (other)
  (let ((value (%dereference cell)))
    (cond ((not (value-cell-p value))
           (unify value other)))))
        
(defmethod (read-only-variable :ordinary-term) ()
  (let ((value (%dereference cell)))
    (cond ((value-cell-p value)
           (values self t))
          (t value))))

(defmethod (read-only-variable :lisp-form) (mode)
  (let ((form (lisp-form (%dereference cell) mode)))
    (cond ((typep form 'source-variable)
	   (make-instance-in-area *prolog-work-area*
				  'source-ro-variable
				  ':cell (%dereference cell)
				  ':name (send form ':name)))
	  (t form))))

(defmethod (read-only-variable :variable-p) ()
  (value-cell-p (%dereference cell)))


(compile-flavor-methods read-only-variable)

(make-instance 'read-only-variable) ;;seems to be needed to really initialize...

;;; Runtime.

(declare (special puser:tvrtle-window))

(define-predicate help
  ((help)
   (lisp-value ?help prolog:*bagel-help*)
   (format t "~%~a" ?help)))

(define-predicate cptop
  ((cptop . ?goals)
   (cp . ?goals)))

(define-predicate cptop
  (:options (:world :graphics))
  ((cptop . ?goals)
   (lisp-command (send puser:tvrtle-window ':clear-screen))
   (cp-bagel . ?goals)))

(define-predicate cp
  ((cp . ?goals)
   (append ?sys0 ?goals (:cycle . ?sys))
   (cpsolve ?sys0 ?sys :nodeadlock)))

(define-predicate cpreduce
  (:options (:world :cp-bf))
  ((cpreduce ((?p . ?args) . ?front0) ?back0 ?front0 ?back1)
   (?p ?args ?back0 ?back1)))

(define-predicate cpreduce
  (:options (:world :cp-df))
  ((cpreduce ((?p . ?args) . ?front1) ?back0 ?front0 ?back0)
   (?p ?args ?front0 ?front1)))

(define-predicate cpstate
  ((cpstate :cycle :nodeadlock :deadlock))
  ((cpstate (? . ?) ?old ?old)))

(define-predicate cpsolve
  (:options (:argument-list (+ * +)))
  (;Reduction...
   (cpsolve ?front0 ?back0 ?)
   (cpreduce ?front0 ?back0 ?front1 ?back1)
   (cut)
   (cpsolve ?front1 ?back1 :nodeadlock))
  (;Empty system...
   (cpsolve (:cycle) () ?)
   (cut))
  (;Suspension...
   (cpsolve (?goal . ?front) (?goal . ?back) ?old)
   (cpstate ?goal ?old ?new)
   (cut)
   (cpsolve ?front ?back ?new)))

(define-predicate :prolog
  ((:prolog ?args ?s ?s) (and . ?args)))

(define-predicate :at
  ((:at ((?p . ?args) . ?) ?s0 ?s)
   (?p ?args ?s0 ?s)))


;;; Graphics.

(define-predicate bagel-stream
  :(options (world graphics))
  ((bagel-stream ?pos0)
   (lisp-value ?instance (make-instance-in-area *prolog-work-area* 'demo-graphics))
   (constrain ?pos0 (graphics-demos-stream-server ?instance ?pos0))))

(define-predicate bagel-stream
  ((bagel-stream . ?)))

(defvar *bagel-pixels-x* 152)
(defvar *bagel-pixels-y* 32)

(defmethod (demo-graphics :bagel) (goal turtle)
  (unwind-protect
    (let* ((turtle-x (first turtle))
	   (turtle-y (second turtle))
	   (turtle-dx (third turtle))
	   (turtle-dy (fourth turtle))
	   (arrow
	     (select (+ turtle-dx turtle-dy turtle-dy)
	       (1 #\right-arrow)
	       (-1 #\left-arrow)
	       (-2 #\uparrow)
	       (2 #+symbolics #\downarrow #-symbolics #\down-arrow)))
	   (window puser:tvrtle-window)
	   (msg (prolog-string "~16s" (lisp-form-1 goal :dont-invoke))))
      (multiple-value-bind (xpos ypos)
	  (compute-bagel-pos turtle-x turtle-y)
	(send window ':set-current-font 1)
	(send window ':set-cursorpos xpos ypos)
	(send window ':draw-rectangle
	      *bagel-pixels-x* *bagel-pixels-y* xpos ypos tv:alu-andca)
	(send window ':tyo arrow)
	(send window ':string-out msg 0 16)
	(send window ':tyo arrow)))
      (send puser:tvrtle-window ':set-current-font 0)))

(defun compute-bagel-pos (bagel-x bagel-y)
  (multiple-value-bind (size-x size-y)
      (send puser:tvrtle-window ':inside-size)
    (let* ((xlen (// size-x *bagel-pixels-x*))
	   (ylen (// size-y *bagel-pixels-y*))
	   (virtual-processor (+ bagel-x (// xlen 2) (* xlen (+ bagel-y (// ylen 2)))))
	   (bagel-processor (\ virtual-processor (1- (* xlen ylen)))))
	  (cond ((< bagel-processor 0)
		 (incf bagel-processor (1- (* xlen ylen)))))
      (values (+ 2 (* *bagel-pixels-x* (\ bagel-processor xlen)))
	      (+ 2 (* *bagel-pixels-y* (// bagel-processor xlen)))))))

(define-predicate cp-bagel
  ((cp-bagel . ?goals0)
   (cpreduce-system ?goals0 (0 0 0 +1) ?sys0 (:cycle . ?sys))
   (bagel-stream ?graph0)
   (cpsolve-bagel ?sys0 ?sys :nodeadlock ?graph0)))

(define-predicate cpsolve-bagel
  ((cpsolve-bagel ((:process . ?args) . ?front0) ?back0 ? ?graph0)
   (cpreduce-bagel ?graph0 ?graph ?front0 ?back0 ?front1 ?back1 . ?args)
   (cut)
   (cpsolve-bagel ?front1 ?back1 :nodeadlock ?graph))
  ((cpsolve-bagel (:cycle) () ? ())
   (cut))
  ((cpsolve-bagel (?goal . ?sys0) (?goal . ?sys) ?old ?graph)
   (cpstate ?goal ?old ?new)
   (cut)
   (cpsolve-bagel ?sys0 ?sys ?new ?graph)))

(define-predicate cpreduce-bagel
  (:options (:world :cp-bf))
  ((cpreduce-bagel ?graph0 ?graph ?front0 ?back0 ?front0 ?back1 (?p . ?args) ?turtle)
   (= ?graph0 ((:bagel (?p . ?args) ?turtle) . ?graph))
   (?p ?args ?temp ())
   (cpreduce-system ?temp ?turtle ?back0 ?back1)))

(define-predicate cpreduce-bagel
  (:options (:world :cp-df))
  ((cpreduce-bagel ?graph0 ?graph ?front1 ?back0 ?front0 ?back0 (?p . ?args) ?turtle)
   (= ?graph0 ((:bagel (?p . ?args) ?turtle) . ?graph))
   (?p ?args ?temp ())
   (cpreduce-system ?temp ?turtle ?front0 ?front1)))

(define-predicate cpreduce-system
  ((cpreduce-system () ? ?sys ?sys))
  ((cpreduce-system (?goal . ?goals) ?turtle (?p-goal . ?sys0) ?sys)
   (cpreduce-system-1 ?goal ?turtle ?p-goal)
   (cpreduce-system ?goals ?turtle ?sys0 ?sys)))

(define-predicate cpreduce-system-1
  ((cpreduce-system-1 (:at ?goal . ?d-turtle) ?turtle (:process ?goal ?n-turtle))
   (cut)
   (move-turtle ?turtle ?d-turtle ?n-turtle))
  ((cpreduce-system-1 ?goal ?turtle (:process ?goal ?turtle))))

(define-predicate move-turtle
  ((move-turtle ?t () ?t))
  ((move-turtle (?x ?y ?dx ?dy) (:forward . ?t0) ?t)
   (sum ?x1 ?x ?dx)
   (sum ?y1 ?y ?dy)
   (move-turtle (?x1 ?y1 ?dx ?dy) ?t0 ?t))
  ((move-turtle (?x ?y ?dx ?dy) ((:forward ?amt) . ?t0) ?t)
   (lisp-value ?x1 (TRUNCATE (+ '?x (* '?dx ?amt))))
   (lisp-value ?y1 (TRUNCATE (+ '?y (* '?dy ?amt))))
   (move-turtle (?x1 ?y1 ?dx ?dy) ?t0 ?t))
  ((move-turtle (?x ?y ?dx ?dy) (:back . ?t0) ?t)
   (difference ?x1 ?x ?dx)
   (difference ?y1 ?y ?dy)
   (move-turtle (?x1 ?y1 ?dx ?dy) ?t0 ?t))
  ((move-turtle (?x ?y ?dx ?dy) (:right . ?t0) ?t)
   (turn ?dx ?dy ?dx1 ?dy1)
   (move-turtle (?x ?y ?dx1 ?dy1) ?t0 ?t))
  ((move-turtle (?x ?y ?dx ?dy) (:left . ?t0) ?t)
   (turn ?dx1 ?dy1 ?dx ?dy)
   (move-turtle (?x ?y ?dx1 ?dy1) ?t0 ?t)))

(define-predicate turn
  ((turn 0 1 -1 0))
  ((turn -1 0 0 -1))
  ((turn 0 -1 1 0))
  ((turn 1 0 0 1)))

;;; Compiler. DEFINE-CP transforms into a predicate of exactly three arguments:
;;; the "real" arglist, head of body goal list, tail of body goal list.
;;; Currently, the goal list will be created before the guard is run.
;;; It could put after the guard but then PROVE-CONJUNCION would be called much
;;; more often.

(define-predicate define-cp
  (:options (:lisp-macro-name define-cp))
  ((define-cp ?name . ?rules)
   (map define-cp-rule ?rules ?cp-rules)
   (define-predicate ?name . ?cp-rules)))

(define-predicate define-cp-rule
  ((define-cp-rule (:options . ?options) (:options . ?options)))
  ((define-cp-rule ((?p . ?args) . ?guard-body) ((?p ?args ?sys0 ?sys) . ?cp-guard))
   (guard-and-body ?guard-body ?guard ?body)
   (optimize-guard ?guard ?cp-guard)
   (append ?sys0 ?body ?sys)))

(define-predicate optimize-guard
  ((optimize-guard () ()))
  ((optimize-guard ((:prolog . ?goals)) ?goals))
  ((optimize-guard ?processes ((cp . ?processes)))))

(define-predicate guard-and-body
  ((guard-and-body ?all ?guard ?body)
   (append ?all ?guard ((cut)) ?body))
  ((guard-and-body ?body () ?body)))

;;; Utilities.

(define-predicate :top-level-predication
  :(options (world concurrent-prolog-top-level))
  ((:top-level-predication ?predication)
   (cases ((atomic ?predication)
           (error ':bad-predication "~s must be a predication (i.e. a list)"
                  ?predication))
          ((variables ?variables ?predication)
	   (variable-names ?variable-names ?predication)
           (cases ((cptop ?predication)
                    (format t "~&OK")
                    (print-bindings ?variable-names ?variables))
                  ((format t "~&No answer") (cut) (false)))))))

(GLOBALIZE 'DEFINE-CP ':PGLOBAL)
(GLOBALIZE 'CPTOP ':PGLOBAL)
(ADD-WORLD :CP-BF)

(compile-flavor-methods read-only-variable)

