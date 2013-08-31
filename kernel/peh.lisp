;;; -*- Mode: Lisp; Package: EH; Base: 10. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


(advise com-top-level-throw :around sg-chain-lossage 0
  (or (errset :do-it nil)
      (sg-abort (process-initial-stack-group current-process))))

(DEFUN add-COMMAND (CHAR function)
  (assure-dispatch-set-up)
  (setf (AREF *COMMAND-DISPATCH-TABLE*
	      (LDB %%KBD-CONTROL-META CHAR)
	      (LDB %%KBD-CHAR (CHAR-UPCASE CHAR)))
	function))


(add-command #\super-f 'com-fail)
(add-command #\super-F 'com-fail)
(add-command #\super-s 'com-succeed)
(add-command #\super-S 'com-succeed)
(add-command #\super-r 'com-retry)
(add-command #\super-R 'com-retry)

(advise eh:com-help :after nil nil
	  (send STANDARD-OUTPUT ':STRING-OUT
		   "

LM-Prolog execution control commands available at predicate frames:
Super-F causes the current predicate to fail.
Super-S causes the current predicate to succeed.
Super-R retries the current predicate.
"))

(defun prolog-frame-p (sg frame)
  (let* ((rp (sg-regular-pdl sg))
	 (function (rp-function-word rp frame))
	 (nargs (rp-number-args-supplied rp frame)))
    (and (> nargs 0)
	 (or (cond ((string-search "CONTINUATION" (arg-name function 0)) 0))
	     (and (> nargs 1)
		  (cond ((string-search "CONTINUATION" (arg-name function 1)) 1)))))))

(defun find-mark (sg frame)
  (let* ((rp (sg-regular-pdl sg))
	 (function (rp-function-word rp frame))
	 (nlocals (fef-number-of-locals function)))
    (dotimes (i nlocals)
      (and (string-equal "MARK" (local-name function i)) (return i)))))

(defun com-fail (SG &rest ignore)
  (cond ((prolog-frame-p sg *current-frame*)
	 (resume-do-it "[Failing]" sg '(false))
	 (comment
	   (LEAVING-ERROR-HANDLER)
	   (SETF (RP-TRAP-ON-EXIT (SG-REGULAR-PDL SG) INNERMOST-VISIBLE-FRAME) 0)
	   (SG-UNWIND-TO-FRAME SG *CURRENT-FRAME* T nil)))
	(t (format t "The current frame does not seem to be an LM-Prolog frame.")))
  nil)

(defun com-succeed (SG &rest ignore)
  (let ((continuation-arg-no (prolog-frame-p sg *current-frame*)))
    (cond (continuation-arg-no
	   (resume-do-it
	     "[Succeeding]" sg (SG-FRAME-ARG-VALUE SG *CURRENT-FRAME* CONTINUATION-ARG-NO)))
	  (t (format t "The current frame does not seem to be an LM-Prolog frame."))))
  nil)

(defun com-retry (SG &rest ignore)
  (cond ((prolog-frame-p sg *current-frame*)
	 (let ((mark-local-no (find-mark sg *current-frame*)))
	   (cond (mark-local-no
		  (let ((mark (SG-FRAME-LOCAL-VALUE SG *CURRENT-FRAME* mark-local-no)))
		    (cond (mark
			   prolog:
			   (let ((*trail-array* (symeval-in-stack-group '*trail-array* eh:sg))
				 (*prolog-work-area*
				   (symeval-in-stack-group '*prolog-work-area* eh:sg))
				 (*vector* (symeval-in-stack-group '*vector* eh:sg)))
			     (link-*trail*-count)
			     (untrail eh:mark)))))
		  (resume-do-it
		    "[Re trying]" sg (GET-FRAME-FUNCTION-AND-ARGS SG *CURRENT-FRAME*)))
		 (t (format t
			    "The current frame does not bind a trail pointer. Retry anyway ")
		    (and (y-or-n-p)
			 (resume-do-it "[Re trying]" sg
			   (GET-FRAME-FUNCTION-AND-ARGS SG *CURRENT-FRAME*)))))))
	(t (format t "The current frame does not seem to be an LM-Prolog frame.")))
  nil)

(defun resume-do-it (msg sg form)
  (format t msg)
  (SG-UNWIND-TO-FRAME-AND-REINVOKE SG *CURRENT-FRAME* form)
  (LEAVING-ERROR-HANDLER)
  (WITHOUT-INTERRUPTS
    (AND *ERROR-HANDLER-RUNNING*
	 (FREE-SECOND-LEVEL-ERROR-HANDLER-SG %CURRENT-STACK-GROUP))
    (STACK-GROUP-RESUME SG NIL)))


;(compile-encapsulations 'com-top-level-throw)

(comment ;;needs to be updated

;;this is a mutilated version of eh:com-search
;;it provides <hand-up> and <hand-down> as commands 
;;to move up and down the Prolog "stack"

(DEFUN COM-prove-previous (SG IGNORE &OPTIONAL (repeat 1) ignore &AUX FRAME)
  (SETQ FRAME
	(do ((count repeat (1- count))	     
	     (frame *current-frame*
		    (DO-named find-frame
			      ((FRAME (SG-PREVIOUS-ACTIVE SG FRAME)
				      (SG-PREVIOUS-ACTIVE SG FRAME))
			       (RP (SG-REGULAR-PDL SG))
			       (NAME))
			      ((NULL FRAME) NIL)
		      (SETQ NAME (FUNCTION-NAME (RP-FUNCTION-WORD RP FRAME)))
		      (AND (COND ((STRINGP NAME) (equal name "prove"))
				 ((SYMBOLP NAME) (eq name 'prolog:prove)))
			   (RETURN-from find-frame FRAME)))))
	    ((or (zerop count) (null frame)) frame)))
  (COND ((NULL FRAME)
	 (FORMAT T "No more calls to Prove~%"))
	(T
	 (SETQ *CURRENT-FRAME* FRAME)
	 (print-predication SG frame))))

(DEFUN COM-prove-next (SG IGNORE &OPTIONAL (repeat 1) ignore &AUX FRAME)
  (SETQ FRAME
	(do ((count repeat (1- count))	     
	     (frame *current-frame*
		    (DO ((FRAME (SG-NEXT-ACTIVE SG FRAME)
				(SG-NEXT-ACTIVE SG FRAME))
			 (RP (SG-REGULAR-PDL SG))
			 (NAME))
			((NULL FRAME) NIL)
		      (SETQ NAME (FUNCTION-NAME (RP-FUNCTION-WORD RP FRAME)))
		      (AND (COND ((STRINGP NAME) (equal name "prove"))
				 ((SYMBOLP NAME) (eq name 'prolog:prove)))
			   (RETURN FRAME)))))
	    ((or (zerop count) (null frame)) frame)))
  (COND ((NULL FRAME)
	 (FORMAT T "No more calls to Prove~%"))
	(T
	 (SETQ *CURRENT-FRAME* FRAME)
	 (print-predication SG frame))))

(defun print-predication (sg frame)
  (let ((predication (catch-error (sg-frame-arg-value sg frame 0)))
	(vector (catch-error (sg-frame-arg-value sg frame 1))))
    (format t "~%Proving: ")
    (PROLOG:PRINT-TOP-LEVEL (prolog:lisp-form predication vector))))

(DEFUN add-COMMAND (CHAR function)
  (setf (AREF COMMAND-DISPATCH-TABLE
	      (LDB %%KBD-CONTROL-META CHAR)
	      (LDB %%KBD-CHAR (CHAR-UPCASE CHAR)))
	function))


(add-command #\hand-up 'com-prove-previous)
(add-command #\hand-down 'com-prove-next)

(advise eh:com-help :after nil nil
	  (FUNCALL STANDARD-OUTPUT ':STRING-OUT
		   "

Prolog stack inspection commands:
™ goes up a Prolog frame to parent predication,
š goes down a Prolog frame to child predication.
"))
)
