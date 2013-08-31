;;; -*- Mode: Lisp; Package: Puser; Base: 10. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;split screen stuff for LM-Prolog and the backtracking turtle

(defvar *prolog-with-turtle-frame*)

tv:
(progn 'compile
(defflavor tvrtle-pane-flavor () (window))

(DEFMETHOD (tvrtle-pane-flavor :END-OF-LINE-EXCEPTION) ()
  ;; Put an "!" in the right margin if called for.
  (OR (ZEROP (SHEET-RIGHT-MARGIN-CHARACTER-FLAG))
      (FUNCALL-SELF ':TYO-RIGHT-MARGIN-CHARACTER CURSOR-X CURSOR-Y #/!))
  ;; Move to left margin only, i.e. wrap around.
  (SHEET-INCREMENT-BITPOS #-symbolics SELF (- CURSOR-X) 0)
  (OR (ZEROP (SHEET-EXCEPTIONS))		;Take care of any residual **more**
      (SHEET-HANDLE-EXCEPTIONS SELF)))

(DEFMETHOD (tvrtle-pane-flavor :END-OF-PAGE-EXCEPTION) ()
  (COND ((NOT (ZEROP (SHEET-END-PAGE-FLAG)))
	 (LET ((M-VP MORE-VPOS))	;SHEET-HOME smashes this, since it moves the cursor
	   ;; Wrap around ONLY.
	   (SHEET-INCREMENT-BITPOS #-symbolics self 0 (- cursor-y))
	   (SETF (SHEET-EXCEPTIONS self) 0)
	   ;; Arrange for more processing next time around
	   (COND ((NULL M-VP))			;No more processing at all
		 (( M-VP 100000)		;More processing delayed?
		  (SETQ MORE-VPOS (- M-VP 100000)))	;Cause to happen next time around
		 (T (SETQ MORE-VPOS (SHEET-DEDUCE-MORE-VPOS SELF)))))))))

(defun prolog-with-turtle (&optional ignore)
  (prolog-without-turtle)
;  (let ((standard-output *turtle-type-in-window*))
;    (prolog:eval-in-window
;     *turtle-type-in-window*
;     '(prolog:top-level-prove-and-show-results '(true))))
  (send *turtle-type-in-window* ':force-kbd-input #\abort)
  (send *turtle-type-in-window* ':clear-screen)
  (customize-turtle)
  *prolog-with-turtle-frame*)

(defun Prolog-without-turtle (&optional ignore) 
  ;(send terminal-io ':force-kbd-input #\rubout)	;symbolics rel. 6
  (cond ((not (boundp '*prolog-with-turtle-frame*))
	 (setq *prolog-with-turtle-frame*
	       (tv:make-window
		 'tv:constraint-frame
		 ':panes
		 `((prolog-pane PROLOG:PROLOG-listener)
		   (tvrtle-pane tv:tvrtle-pane-flavor
				:font-map
				,(list fonts:medfnb fonts:cptfont)
				:label "Turtle"))
		 ':constraints
		 `((main . ((tvrtle-pane prolog-pane)
			    ((tvrtle-pane .6))
			    ((prolog-pane :even)))))
		 ':expose-p t))
	 (tvrtlify-window
	   (send *prolog-with-turtle-frame* ':get-pane 'tvrtle-pane))
	 (setq *turtle-type-in-window*
	       (send *prolog-with-turtle-frame* ':get-pane 'prolog-pane))
;	 (let ((string "(pkg-goto ':puser)"))
;	   (dotimes (i (string-length string))
;	     (send *turtle-type-in-window* ':force-kbd-input (aref string i))))
	 ))
;  (send *turtle-type-in-window* ':force-kbd-input #.prolog:*roman-ii*)
  (send *turtle-type-in-window* ':select) ;;all user tyi after Roman-II
  *prolog-with-turtle-frame*)

(defun tvrtlify-window (window)
  (send window ':set-save-bits t)
  (set-in-instance window 'tv:char-aluf tv:alu-xor)
  (send (first (symeval-in-instance window 'tv:blinker-list)) ':set-visibility nil)
  (send window ':set-label "Turtle")
  (setq tvrtle-window window))

(defun customize-turtle ()
  (startdisplay) (xordown) (wrap))
