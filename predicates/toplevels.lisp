;;; -*- Mode: Lisp; Package: Prolog; Base: 10; Options: ((World System)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;Various top-levels for LM-Prolog.

;(define-predicate print-and-space 
;  ((print-and-space ?term)
;   (lisp-command (FUNCALL (OR PRIN1 #'PRIN1) '?term) :invoke)
;   (tyo #/  t)))

(define-predicate print-bindings 
  ((print-bindings ?variables-names)
   (lisp-predicate (top-level-continuation '?variables-names))))

(define-predicate variable-names 
  ((variable-names ?names ?variables)
   (lisp-value ?names '?variables :dont-invoke)))

;;This is the usual one.
(define-predicate :top-level-predication (:options (:world :ordinary-top-level))
  ((:top-level-predication ?predication)
   (cases ((atomic ?predication)
           (error ':bad-predication "~s must be a predication (i.e. a list)"
                  ?predication))
          ((variables ?variables ?predication)
	   (variable-names ?variable-names ?variables)
;           (cases (?predication
;                    (format t "~&OK")
;                    (print-bindings ?variable-names))
;                  ((format t "~&No answer") (cut) (false)))
           ?predication
	   (print-bindings ?variable-names)
	   )))
;  ((:top-level-predication ?)
;   (format t "~&No more answers")
;   (fail))
  )

;;This presents only unique answers.
(define-predicate :top-level-predication
  (:options (:world :unique-answers-top-level))
  ((:top-level-predication ?predication)
   (cases ((atomic ?predication)
           (error ':bad-predication "~s must be a predication (i.e. a list)"
                  ?predication))
          ((variables ?variables ?predication)
           (variable-names ?variable-names ?variables)
           (lazy-set-of ?answers ?variables ?predication)
;           (cases ((member ?answer ?answers)
;                   (format t "~&OK")
;                   (print-bindings ?variable-names))
;                  ((format t "~&No answer") (cut) (false)))
           (member ?variables ?answers)
	   (print-bindings ?variable-names)
	   )))
;  ((:top-level-predication ?)
;   (format t "~&No more answers")
;   (fail))
  )

(define-predicate :ordinary-top-level (:options (:world :unique-answers-top-level))
  ((:ordinary-top-level) (remove-world :unique-answers-top-level)))

;;This one presents only unique answers and computes subsequent ones in 
;;background process.
(define-predicate :top-level-predication (:options (:world :compute-ahead-top-level))
  ((:top-level-predication ?predication)
   (cases ((atomic ?predication)
           (error ':bad-predication "~s must be a predication (i.e. a list)"
                  ?predication))
          ((variables ?variables ?predication)
           (variable-names ?variable-names ?variables)
           (eager-set-of ?answers ?variables ?predication)
;           (cases ((member ?answer ?answers)
;                   (format t "~&OK")
;                   (print-bindings ?variable-names))
;                  ((format t "~&No answer") (cut) (false)))
           (member ?variables ?answers)
	   (print-bindings ?variable-names)
	   )))
;  ((:top-level-predication ?)
;   (format t "~&No more answers")
;   (fail))
  )

(define-predicate :ordinary-top-level (:options (:world :compute-ahead-top-level))
  ((:ordinary-top-level) (remove-world :compute-ahead-top-level)))

;;Alan Robinson argued for this top level for Prolog...
;(define-predicate :top-level-predication (:options (:world :lazy-set-top-level))
; ((:top-level-predication ?problem)
;  (cases ((= ?problem (?term . (?predicator . ?arguments)))
;          (lazy-set-of ?answers ?term (?predicator . ?arguments))
;          (cases ((identical ?term call)
;                  (cases ((= ?answers (? . ?)) (format t "~&OK"))
;                         ((format t "~&No answer"))))
;                 ((format t "~&(")
;                  (map print-and-space ?answers)
;                  (format t ")"))))
;         ((format t "~&~S is not of the form (?term . ?predication)"
;                  ?problem)))
;  (fail) ;;to make hand-down barf
;  ))

;(define-predicate :ordinary-top-level (:options (:world :lazy-set-top-level))
;  ((:ordinary-top-level) (remove-world :lazy-set-top-level)))

;;Parallel Prolog top-level.
(define-predicate :top-level-predication
  (:options (:world :parallel-prolog-top-level))
  ((:top-level-predication ?predication)
   (variables ?variables ?predication)
   (variable-names ?variable-names ?variables)
;   (or (and (parallel-prove ?predication)
;            (format t "~&OK")
;            (print-bindings ?variable-names))
;       (and (format t "~&No answer") (false)))
   (parallel-prove ?predication)
   (print-bindings ?variable-names)
   ))

(define-predicate :ordinary-top-level (:options (:world :parallel-prolog-top-level))
  ((:ordinary-top-level)
   ;;can't use remove-world since this may change the universe before computing it!!!
   (lisp-command (set-universe (delq ':parallel-prolog-top-level *universe*)))))

