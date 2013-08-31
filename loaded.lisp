;;; -*- Mode:LISP; Package:PROLOG; Base:10 -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;; LM-Prolog loaded.

;Protect us from possible area bug.
#+Symbolics
(PROLOG:PROLOG-STRING "~S" " ")

;Protect us from user doing (UNADVISE).
(setq si:*advised-functions* ())

(sstatus feature LM-PROLOG)

(format t "~%LM-Prolog for LMI Release 3.0")

(format t "~%Type ~:C for help." #\super-help)

(pkg-goto ':puser #+commonlisp t)
