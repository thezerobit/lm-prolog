;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; Options:((WORLD GRAPHICS-DEMOS)); -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;; A stream-based graphics facility.

puser:
(declare (special tvrtle-window))

(defflavor demo-graphics ((xcor 0) (ycor 0) (dxcor 1) (dycor 1)
			  (SCREEN (tv:sheet-get-screen puser:tvrtle-window)))
	   ()
  :gettable-instance-variables
  :settable-instance-variables
  :initable-instance-variables)

(defmacro with-coerced (let-list &body body)
  `(let ,(coerce-pair (caar let-list) (cadar let-list) (caadr let-list) (cadadr let-list))
     ,@body))

(defmacro with-coerced-d (let-list &body body)
  `(let ,(coerce-d-pair (caar let-list) (cadar let-list) (caadr let-list) (cadadr let-list))
     ,@body))

(eval-when (compile eval load)
(defun coerce-pair (cx0 x0 cy0 y0)
  `((,cx0 (fix (+ xcor (* dxcor ,x0)))) (,cy0 (fix (+ ycor (* dycor ,y0))))))

(defun coerce-d-pair (cx0 x0 cy0 y0)
  `((,cx0 (fix (* dxcor ,x0))) (,cy0 (fix (* dycor ,y0))))))


(defmethod (demo-graphics :define-coords) (x0 y0 dx dy)
  (remind self ':set-xcor xcor)
  (remind self ':set-ycor ycor)
  (remind self ':set-dxcor dxcor)
  (remind self ':set-dycor dycor)
  (setq xcor x0 ycor y0 dxcor dx dycor dy)
  t)

(defmethod (demo-graphics :line) (x0 y0 x1 y1)
  (with-coerced ((cx0 x0) (cy0 y0))
    (with-coerced ((cx1 x1) (cy1 y1))
      (remind puser:tvrtle-window ':draw-line cx0 cy0 cx1 cy1)
      (send puser:tvrtle-window ':draw-line cx0 cy0 cx1 cy1)))
  t)

(defmethod (demo-graphics :point) (x0 y0)
  (with-coerced ((cx0 x0) (cy0 y0))
    (send puser:tvrtle-window ':draw-point cx0 cy0))
  t)

(defmethod (demo-graphics :rectangle) (dx dy x0 y0)
  (with-coerced ((cx0 x0) (cy0 y0))
    (with-coerced-d ((cdx dx) (cdy dy))
      (remind puser:tvrtle-window ':draw-rectangle cdx cdy cx0 cy0)
      (send puser:tvrtle-window ':draw-rectangle cdx cdy cx0 cy0)))
  t)

(defmethod (demo-graphics :digit) (font char x0 y0)
  (send self ':char font (+ #/0 (lisp-form-1 char ':invoke)) x0 y0))

(defmethod (demo-graphics :char) (font char x0 y0) 
  (with-coerced ((cx0 x0) (cy0 y0))
    (let ((font-object (or (get font ':font)
			   (setf (get font ':font)
				 (send SCREEN ':parse-font-descriptor font)))))
      (remind puser:tvrtle-window ':draw-char font-object char cx0 cy0)
      (send puser:tvrtle-window ':draw-char font-object char cx0 cy0)))
  t)

(defmethod (demo-graphics :text) (text x0 y0)
  (with-coerced ((cx0 x0) (cy0 y0))
    (remind puser:tvrtle-window ':set-cursorpos cx0 cy0)
    (send puser:tvrtle-window ':set-cursorpos cx0 cy0)
    (remind puser:tvrtle-window ':string-out text)
    (send puser:tvrtle-window ':string-out text))
  t)

(defmethod (demo-graphics :centered-text) (text x0 x1 y0) 
  (with-coerced ((cx0 x0) (cy0 y0))
    (with-coerced ((cx1 x1) (ignore y0))
      (let ((msg #+symbolics ':display-centered-string #-symbolics ':string-out-centered))
	(remind puser:tvrtle-window msg text cx0 cx1 cy0)
	(send puser:tvrtle-window msg text cx0 cx1 cy0))))
  t)

(defmethod (demo-graphics :absolute-size) (x0 y0)
  (multiple-value-bind (xs ys)
      (send puser:tvrtle-window ':inside-size)
    (and (unify x0 xs) (unify y0 ys))))

(defmethod (demo-graphics :fix-mouse) (prompt x0 y0)
  (multiple-value-bind (raw-x raw-y)
      (send self ':raw-mouse prompt)
    (and (unify x0 (fix raw-x)) (unify y0 (fix raw-y)))))

(defmethod (demo-graphics :raw-mouse) (prompt)
  tv:
  (with-mouse-grabbed
    (process-wait "Button up" #'(lambda () (zerop mouse-last-buttons)))
    (mouse-set-blinker-definition ':character 0 0 ':on ':set-character 20.)
    (setq who-line-mouse-grabbed-documentation prolog:prompt)
    (process-wait "Click" #'(lambda () (not (zerop mouse-last-buttons))))
    (multiple-value-bind (dx dy)
	(sheet-calculate-offsets puser:tvrtle-window prolog:screen)
      (values (// (- mouse-x dx prolog:xcor) prolog:dxcor)
	      (// (- mouse-y dy prolog:ycor) prolog:dycor)))))

(defmethod (demo-graphics :clear-screen) ()
  (send puser:tvrtle-window ':clear-screen)
  t)

(define-predicate graphics-demos-stream
  :(options (world graphics))
  ((graphics-demos-stream ?pos0)
   (lisp-value ?instance (make-instance-in-area *prolog-work-area* 'demo-graphics))
   (graphics-demos-stream-server ?instance ((:clear-screen) . ?pos0))))

(define-predicate graphics-demos-stream
  ((graphics-demos-stream . ?)))

(define-predicate graphics-demos-stream-server
  :(options (world graphics))
  ((graphics-demos-stream-server ? ()) (cut))
  ((graphics-demos-stream-server ?instance (?msg . ?pos0))
   (lisp-predicate (apply '?instance '?msg))
   (constrain ?pos0 (graphics-demos-stream-server ?instance ?pos0))))
