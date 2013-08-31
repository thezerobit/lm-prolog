;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;; This file provides missing parts of various systems software.

#+symbolics
(progn 'compile
(defsubst consp (x) (not (atom x)))

(defsubst contents (x) (cdr x))

(globalize 'consp ':pglobal)

(globalize 'contents ':pglobal)

(defun faked-ap-1-force (array i)
  (%make-pointer-offset
    dtp-locative
    (lexpr-funcall #'aloc array
		   (mapcar #'* (array-dimensions array) (circular-list 0)))
    i))

(defun faked-eql (x y)
  (and (numberp x) (numberp y) (= x y))))

(defun faked-nset-difference (set decrement)
  (mapc #'(lambda (x) (setq set (delq x set))) decrement)
  set)

(defun make-pixel-array-faked (x-dim y-dim &rest make-array-args)
  (lexpr-funcall 'make-array (list x-dim y-dim) make-array-args))

(defun pixel-array-width-faked (pixel-array)
  (array-dimension-n 1 pixel-array))

(defun pixel-array-height-faked (pixel-array)
  (array-dimension-n 2 pixel-array))

(defun def-faked (f f-faked &optional (glob-p t))
  (cond ((not (fdefinedp f))
	 (setf (fsymeval f) f-faked)
	 (and glob-p (globalize f ':pglobal)))))

(def-faked 'eql 'faked-eql)
(def-faked 'nset-difference 'faked-nset-difference)
(def-faked 'ap-1-force 'faked-ap-1-force)
(def-faked 'ar-2-reverse 'ar-2)
(def-faked 'as-2-reverse 'as-2)
(def-faked 'truncate 'fix)
(def-faked 'round 'fixr)
(def-faked 'make-pixel-array 'make-pixel-array-faked)
(def-faked 'pixel-array-width 'pixel-array-width-faked)
(def-faked 'pixel-array-height 'pixel-array-height-faked)

(defsubst careful-first (x)
  (cond ((consp x) (first x))
        (t x)))

(defsubst careful-rest1 (x)
  (cond ((consp x) (rest1 x))
        (t x)))

(defsubst last-element (x) (first (last x)))

(defmacro select-processor-faked (&rest clauses)
  (let ((cadr-clause (assq ':cadr clauses)))
    (cons 'progn (cdr cadr-clause))))

(def-faked 'select-processor 'select-processor-faked)

;;; Symbolics release 6.

(defmacro push-in-area-faked (item list-name area)
  `(setf ,list-name (cons-in-area ,item ,list-name ,area)))

(def-faked 'push-in-area 'push-in-area-faked)

(def-faked 'compile-encapsulations 'prog1)

(cond ((not (boundp 'si:macro-compiled-program))
       (defvar si:macro-compiled-program)
       (si:forward-value-cell 'si:macro-compiled-program 'compiled-function-area)))

(defun file-declaration-faked (thing declaration)
  (caddar (mem #'(lambda (item element)
		   (and (eq (car element) (cdr item))
			(eq (cadr element) (car item))))
	       (cons thing declaration)
	       compiler:file-local-declarations)))

(defun file-declare-faked (thing declaration value)
  (push (list declaration thing value) compiler:file-local-declarations))

(defun forward-function-cell-faked (from to)
  (or (eq (follow-cell-forwarding (function-cell-location from) t)
	  (follow-cell-forwarding (function-cell-location to) t))
      (%p-store-tag-and-pointer (follow-cell-forwarding (function-cell-location from) t)
				dtp-one-q-forward
				(function-cell-location to))))

(def-faked 'forward-function-cell 'forward-function-cell-faked)

(def-faked 'compiler:file-declare 'file-declare-faked nil)

(def-faked 'compiler:file-declaration 'file-declaration-faked nil)

(eval-when (compile eval load)
  (pkg-find-package "LT" t))

(or (get '*catch 'lt:mapforms)
    (setf (get '*catch 'lt:mapforms) (get 'setq 'lt:mapforms)))

#+3600
(progn 'compile
(defmacro nilmacro nil nil)

(or (get 'si:%frame-consing-done 'compiler:built-in)
    (def-faked 'si:%frame-consing-done 'nilmacro nil))
)
