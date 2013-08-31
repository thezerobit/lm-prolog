;;; -*- Mode: Lisp; Package: Puser; Base: 10. ; Options: ((World Turtle)); -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


(define-predicate help
  ((help)
   (lisp-value ?help prolog:*turtle-help* )
   (format t "~%~a" ?help)))

;;; Examples. These generate difference lists of Turtle commands.

(define-predicate poly
  (:options (:argument-list (commands commands-end edges size &optional ignore)))
  ((poly ?com ?com ?edges ?)
   ( ?edges 1))
  ((poly ?com0 ?com ?edges ?size)
   (> ?edges 1)
   (quotient ?angle 360. ?edges)
   (poly ?com0 ?com ?angle ?edges 0 ?size))
  ((poly ?com ?com ? ?edges ?edges ?))
  ((poly ((:forward ?size) . ?com0) ?com ?angle ?edges ?fewer ?size)
   (= ?com0 ((:right ?angle) . ?com1))
   (< ?fewer ?edges)
   (sum ?more ?fewer 1)
   (poly ?com1 ?com ?angle ?edges ?more ?size)))
  
(define-predicate circle
  (:options (:argument-list (commands commands-end +size)))
  ((circle ?com0 ?com ?size) (= ?com0 ((:circle ?size) . ?com))))

;Just a simple demo.
(define-predicate draw-polygons
  ((draw-polygons)
   (turtle-stream ?s)
   (member ?n (3 4 5 6 7 8 9 10))
   (poly ?s () ?n 50.)))

;;; New cleaned-up Turtle interface to logic.
prolog:
(progn 'compile
(define-predicate puser:turtle-stream
  :(options (world graphics))
  ((puser:turtle-stream ?pos0 ())
   (puser:turtle-stream ?pos0))
  ((puser:turtle-stream ?pos0)
   (lisp-value ?instance (make-instance-in-area *prolog-work-area* 'puser:turtle-stream)
	       )
   (turtle-stream-server ?instance ((:startdisplay) . ?pos0))))

(define-predicate puser:turtle-stream
  ((puser:turtle-stream . ?)))

(define-predicate puser:turtle-stream-concurrent
  :(options (world graphics))
  ((puser:turtle-stream-concurrent ?pos0 ((:unlock)))
   (lisp-value ?instance (make-instance-in-area *prolog-work-area* 'puser:turtle-stream)
	       )
   (turtle-stream-server ?instance ((:lock) . ?pos0))))

(define-predicate turtle-stream-server
  :(options (world graphics))
  ((turtle-stream-server ? ()) (cut))
  ((turtle-stream-server ?instance (?msg . ?pos0))
   (lisp-predicate (apply '?instance '?msg)) ;was :invoke
   (constrain ?pos0 (turtle-stream-server ?instance ?pos0))))
)

;;Compatibility.
(defvar *tvstep 1)

(defvar pi-over-180 (// 3.14159265 180.0))

(defvar *turtle-lock* nil)

;;These three are called directly from LMP: LIBRARY; SPLIT
(defun startdisplay nil nil)

(defun xordown nil nil)

(defun wrap nil nil)

(defun turtle-lock ()
  (or (%store-conditional (locf *turtle-lock*) nil current-process)
      (condition-case ()			;If time out then go ahead and clobber...
	  (process-lock (locf *turtle-lock*) nil "Turtle" #-symbolics 70.)
	(error (setq *turtle-lock* nil)
	       (turtle-lock)))))

(defun turtle-unlock ()
  (%store-conditional (locf *turtle-lock*) current-process nil))

(defflavor turtle-stream
	   (*xcor				;X coordinate (in pixels)
	    *ycor				;Y coordinate (in pixels)
	    *xoff				;Add this to *xcor
	    *yoff				;Add this to *ycor
	    *theta				;Direction (in degrees)
	    *cosine				;Cosine of *theta
	    *sine				;Sine of *theta
	    *visibility				;Whether cursor is visible
	    *window				;Our window
	    )
	   ()
  :settable-instance-variables :initable-instance-variables)

;(defmethod (turtle-stream :lock) ()
;  (prolog:remind-call 'turtle-unlock)
;  (turtle-lock)
;  (placeturtle '(0 0 0)))

;(defmethod (turtle-stream :unlock) ()
;  (prolog:remind-call 'placeturtle (prolog:prolog-list *xcor *ycor *heading))
;  (prolog:remind-call 'turtle-lock)
;  (turtle-unlock))

(defmethod (turtle-stream :startdisplay) ()
  (multiple-value-bind (width height)
      (send tvrtle-window ':inside-size)
    (setq *xcor 0 *ycor 0 *theta 0 *cosine 1.0 *sine 0.0
	  *visibility t *window tvrtle-window
	  *xoff (// width 2) *yoff (// height 2)))
  (send *window ':clear-screen)
  (prolog:remind self ':$show-cursor)
  (send self ':$show-cursor)
  t)

(defmethod (turtle-stream :startgrammar) ()
  (prolog:remind self ':$show-cursor)
  (send self ':$show-cursor)
  (send self ':hideturtle)
  (setq *yoff 10 *theta 90. *cosine 0.0 *sine 1.0))

(defmethod (turtle-stream :$show-cursor) ()
  (cond (*visibility
	 (let ((cos10 (round (* *cosine 10))) (sin10 (round (* *sine 10))))
	   (let ((x1 (+ *xoff *xcor (- cos10) (- sin10))) (y1 (+ *yoff *ycor (- sin10) (+ cos10)))
		 (x2 (+ *xoff *xcor cos10)) (y2 (+ *yoff *ycor sin10))
		 (x3 (+ *xoff *xcor (- cos10) (+ sin10))) (y3 (+ *yoff *ycor (- sin10) (- cos10))))
	     (send *window ':draw-triangle x1 y1 x2 y2 x3 y3))))))

(defmethod (turtle-stream :hideturtle) ()
  (cond (*visibility
	 (prolog:remind self ':set-*visibility t)
	 (setq *visibility nil)))
  t)

(defmethod (turtle-stream :showturtle) ()
  (cond ((not *visibility)
	 (prolog:remind self ':set-*visibility nil)
	 (setq *visibility t)))
  t)

(defmethod (turtle-stream :$forward) (steps)
  (let ((xcor (+ *xcor (round (* *cosine steps))))
	(ycor (+ *ycor (round (* *sine steps)))))
    (send self ':$show-cursor)
    (send *window ':draw-line (+ *xcor *xoff) (+ *ycor *yoff) (+ xcor *xoff) (+ ycor *yoff))
    (setq *xcor xcor *ycor ycor)
    (send self ':$show-cursor)))

(defmethod (turtle-stream :$right) (angle)
  (send self ':$show-cursor)
  (setq *theta (\ (+ *theta angle) 360.)
	*cosine (cos (* pi-over-180 (float *theta)))
	*sine (sin (* pi-over-180 (float *theta))))
  (send self ':$show-cursor))

(defmethod (turtle-stream :$setturtle) (xcor ycor theta draw-p)
  (cond ((or ( xcor *xcor) ( ycor *ycor) ( theta *theta))
	 (send self ':$show-cursor)
	 (and draw-p (send *window ':draw-line (+ *xcor *xoff) (+ *ycor *yoff) (+ xcor *xoff) (+ ycor *yoff)))
	 (setq *xcor xcor *ycor ycor)
	 (cond (( theta *theta)
		(setq *theta (\ theta 360.)
		      *cosine (cos (* pi-over-180 (float *theta)))
		      *sine (sin (* pi-over-180 (float *theta))))))
	 (send self ':$show-cursor))))


(defmethod (turtle-stream :forward) (steps)
  (prolog:remind self ':$forward (- steps))
  (send self ':$forward steps)
  t)

(defmethod (turtle-stream :back) (steps)
  (prolog:remind self ':$forward steps)
  (send self ':$forward (- steps))
  t)

(defmethod (turtle-stream :right) (steps)
  (prolog:remind self ':$right (- steps))
  (send self ':$right steps)
  t)

(defmethod (turtle-stream :left) (steps)
  (prolog:remind self ':$right steps)
  (send self ':$right (- steps))
  t)

(defmethod (turtle-stream :here) (xcor ycor theta)
  (and (prolog:unify xcor *xcor)
       (prolog:unify ycor *ycor)
       (prolog:unify theta *theta)))

(defmethod (turtle-stream :setturtle) (xcor ycor theta)
  (prolog:remind self ':$setturtle *xcor *ycor *theta t)
  (send self ':$setturtle xcor ycor theta t)
  t)

(defmethod (turtle-stream :placeturtle) (xcor ycor theta)
  (prolog:remind self ':$setturtle *xcor *ycor *theta nil)
  (send self ':$setturtle xcor ycor theta nil)
  t)

;;The grammar kit needs to display a centered label and skip vertically after.
(defmethod (turtle-stream :markv) (text)
  (prolog:remind self ':$markv text *ycor)
  (send self ':$markv text nil)
  t)

(defmethod (turtle-stream :$markv) (text up)
  (let ((text (string text)))
    (send self ':$show-cursor)
    (cond ((not up)
	   (send *window ':set-cursorpos
		 (- (+ *xoff *xcor) (// (send *window ':string-length text) 2))
		 (+ 5 (+ *yoff *ycor)))
	   (send *window ':string-out text)
	   (incf *ycor 18.))
	  (t (setq *ycor up)
	     (send *window ':set-cursorpos
		   (- (+ *xoff *xcor) (// (send *window ':string-length text) 2))
		   (+ 5 (+ *yoff *ycor)))
	     (send *window ':string-out text)))
    (send self ':$show-cursor)))

(defmethod (turtle-stream :circle) (rad)
  (prolog:remind self ':$circle rad)
  (send self ':$circle rad)
  t)

(defmethod (turtle-stream :$circle) (rad)
 (send *window ':draw-circle (+ *xoff *xcor) (+ *yoff *ycor) rad))
