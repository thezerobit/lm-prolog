;;; -*- Mode: Lisp; Package: Prolog; Base: 8. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;; This file contains code to replace micro-coded primitives of LM-Prolog.

;To go away when we switch to lexical closures.
#-LEXICAL
(defsubst %invoke (x) (apply (car x) (cdr x)))

(defmacro %dereference (x)
  (cond ((symbolp x)
         `(cond ((value-cell-p ,x) (contents ,x)) (t ,x)))
	((and (consp x)
	      (memq (car x)
		    '(quote function prolog-cons prolog-list prolog-list*)))
	 x)
        (t `(let ((x1 ,x))
              (cond ((value-cell-p x1) (contents x1)) (t x1))))))

(defmacro %reference (x)
  (cond ((symbolp x)
         `(cond ((value-cell-p ,x)
                 (%make-pointer dtp-external-value-cell-pointer ,x))
                (t ,x)))
	((and (consp x)
	      (memq (car x)
		    '(quote function prolog-cons prolog-list prolog-list*)))
	 x)
        (t `(let ((x1 ,x))
              (cond ((value-cell-p x1)
                     (%make-pointer dtp-external-value-cell-pointer x1))
                    (t x1))))))

#-3600
(progn 'compile
(defun %cell (name)
  (let ((cell (%make-pointer dtp-locative (cons-in-area nil name *prolog-work-area*))))
    (setf (contents cell) cell)))

(defun %cell0 ()
  (let ((cell (%make-pointer dtp-locative (SI:%MAKE-LIST NIL *prolog-work-area* 1))))
    (setf (contents cell) cell)))

)

#+3600
(progn 'compile
(defun %prolog-list (l &rest elements)
  (without-interrupts
   (let ((cons (si:%allocate-list-block l (or *prolog-work-area* default-cons-area))))
     (do ((cell cons (1+ cell))
	  (l l (1- l))
	  (elements elements (cdr elements)))
	 ((cond ((= l 1)
		 (si:%p-store-cdr-and-contents cell (%reference (car elements)) cdr-nil)
		 t)))		 
       (si:%p-store-cdr-and-contents cell (%reference (car elements)) cdr-next))
     (%make-pointer dtp-list cons))))

(defun %prolog-list* (l &rest elements)
  (without-interrupts
   (let ((cons (si:%allocate-list-block l (or *prolog-work-area* default-cons-area))))
     (do ((cell cons (1+ cell))
	  (l l (1- l))
	  (elements elements (cdr elements)))
	 ((cond ((= l 2)
		 (si:%p-store-cdr-and-contents cell (%reference (car elements)) cdr-normal)
		 (si:%p-store-cdr-and-contents (1+ cell) (%reference (cadr elements)) cdr-nil)
		 t)))		 
       (si:%p-store-cdr-and-contents cell (%reference (car elements)) cdr-next))
     (%make-pointer dtp-list cons))))

(defun prolog-cons (x y)
  (without-interrupts
   (let ((cons (si:%allocate-list-block 2 (or *prolog-work-area* default-cons-area))))
     (si:%p-store-cdr-and-contents cons (%reference x) cdr-normal)
     (si:%p-store-cdr-and-contents (1+ cons) (%reference y) cdr-nil)
     (%make-pointer dtp-list cons))))

(defun %cell (name)
  (without-interrupts
   (let* ((cons (si:%allocate-list-block 2 (or *prolog-work-area* default-cons-area)))
	  (pointer (%make-pointer dtp-locative cons)))
     (si:%p-store-cdr-and-contents cons pointer cdr-normal)
     (si:%p-store-cdr-and-contents (1+ cons) name cdr-nil)
     pointer)))

(defun %cell0 ()
  (without-interrupts
   (let* ((cons (si:%allocate-list-block 1 (or *prolog-work-area* default-cons-area)))
	  (pointer (%make-pointer dtp-locative cons)))
     (si:%p-store-cdr-and-contents cons pointer cdr-nil)
     pointer)))

)

(defsubst %uvar-p (x) (memq (%data-type x) '(#.dtp-locative  #.dtp-instance)))

(defsubst make-unbound (value-cell) (%p-store-contents value-cell value-cell))

;Code depends on this returning NIL.
(deffun %untrail (mark)
  (cond ((> *trail* mark)
         (let ((item (array-pop *trail-array*)))
           (cond ((value-cell-p item) (make-unbound item))
                 (t (invoke item))))
         (%untrail mark))))

(defsubst nth-element (index vector)
  (%p-contents-offset vector index))

(defsubst %unify-term-with-term (x y) (unify x y))

(defmacro bind-cell (x y)
  (cond ((atom x) `(let () (setf (contents ,x) (%reference ,y)) (trail ,x)))
	(t `(let ((bind-cell-temp ,x))
	      (setf (contents bind-cell-temp) (%reference ,y))
	      (trail bind-cell-temp)))))

(DEFINE-DISPATCH-TABLE %CONSTRUCT (TEMPLATE) ((CDR TEMPLATE)) ((CAR TEMPLATE))
		       8. ':initial-value #+3600 #'prog1 #-3600 #'list*)

(DEFINE-DISPATCH-ENTRY %CONSTRUCT 1 (TARGS)
  (let ((cell (%cell (REST1 TARGS))))
    (setf (nth-element (FIRST TARGS) *vector*) cell)
    cell))

(DEFINE-DISPATCH-ENTRY %CONSTRUCT 2 (TARGS)
  (nth-element (FIRST TARGS) *vector*))

(ALTER-DISPATCH-ENTRY %CONSTRUCT 3 '%CONSTRUCT3)

(defsubst %construct3 (TARGS)
  ;;this could be more clever about CDR-coding
  (prolog-cons (%construct (FIRST TARGS)) (%construct (REST1 TARGS))))
  
(ALTER-DISPATCH-ENTRY %CONSTRUCT 4 '%CONSTRUCT4)

(defsubst %construct4 (TARGS)
  (let ((cell (%cell (REST1 TARGS))))
    (setf (nth-element (FIRST TARGS) *vector*) cell)
    (make-instance-in-area *prolog-work-area* 'read-only-variable
                           ':cell cell)))

(ALTER-DISPATCH-ENTRY %CONSTRUCT 5 '%CONSTRUCT5)

(defsubst %construct5 (TARGS)
  (let ((cell (nth-element (FIRST TARGS) *vector*)))
    (cond ((value-cell-p cell)
	   (make-instance-in-area *prolog-work-area* 'read-only-variable
				  ':cell cell))
	  (t cell))))

(alter-dispatch-entry %construct 6 '%construct6)

(defsubst %construct6 (targs)
  (make-instance-in-area *prolog-work-area* 'read-only-variable
			 ':cell (%cell targs)))

(alter-dispatch-entry %construct 7 '%cell)

(define-dispatch-table %unify-term-with-template (term template) (term (cdr template))
		       ((car template))
		       8.)

(alter-dispatch-entry %unify-term-with-template 0 'unify-without-occur-check)

(define-dispatch-entry %unify-term-with-template 1 (term targs)
  (setf (nth-element (first targs) *vector*) term)
  t)

(define-dispatch-entry %unify-term-with-template 2 (term targs)
  (unify term (%dereference (nth-element (first targs) *vector*))))

(define-dispatch-entry %unify-term-with-template 3 (term targs)
  (cond ((consp term)
	 (and (%unify-term-with-template (first term) (first targs))
	      (%unify-term-with-template (rest1 term) (rest1 targs))))
	((%uvar-p term) ;;otherwise don't bother to construct the term 
	 (bind-cell-check term (%construct3 targs)))))

(define-dispatch-entry %unify-term-with-template 4 (term targs)
  (cond ((value-cell-p term)
	 (bind-cell term (%construct4 targs)))
	(t nil)))

(define-dispatch-entry %unify-term-with-template 5 (term targs)
  (let ((old-value (%dereference (nth-element (first targs) *vector*))))
    (cond ((value-cell-p term)
	   (cond ((value-cell-p old-value)
		  (bind-cell term
			     (make-instance-in-area *prolog-work-area*
						    'read-only-variable
						    ':cell old-value)))
		 (t (bind-cell term old-value))))
	  ((value-cell-p old-value) nil)
	  (t (unify old-value term)))))

(define-dispatch-entry %unify-term-with-template 6 (term targs)
  (cond ((value-cell-p term)
	 (bind-cell term (%construct6 targs)))))

(define-dispatch-entry %unify-term-with-template 7 (ignore ignore)
  t)

;;Unifyers come in varying degree of specialization...

;;VARIABLE and not-PREVENT
(defun bind-cell-without-occur-check (x y)
  (cond ((eq x y))
	((value-cell-p x) (bind-cell x y))
	((value-cell-p y) (bind-cell y x))
	((send x ':unify y))))

;;VARIABLE and PREVENT
(defun bind-cell-with-occur-check (x y)
  (cond ((eq x y))
	((value-cell-p x) (and (occur-check x y) (bind-cell x y)))
	((value-cell-p y) (bind-cell y x))
	((send x ':unify y))))

;;NOT-LIST and NOT-VARIABLE and NOT-PREVENT
(defsubst %uvar-constant (x y)
  (select (%data-type x)
    (dtp-locative (bind-cell x y))
    (dtp-instance (send x ':unify y))
    (otherwise (equal x y))))

;;NOT-LIST and NOT-VARIABLE and PREVENT
(defsubst %uvar-constant-occur-check (x y)
  (select (%data-type x)
    (dtp-locative (and (occur-check x y) (bind-cell x y)))
    (dtp-instance (send x ':unify y))
    (otherwise (equal x y))))

;;NOT-LIST and NOT-LIST
(defsubst %uvar (x y) 
  (cond ((= dtp-locative (%data-type x)) (bind-cell x y))
        ((= dtp-locative (%data-type y)) (bind-cell y x))
        ((= dtp-instance (%data-type x)) (send x ':unify y))
        ((= dtp-instance (%data-type y)) (send y ':unify x))
        ((equal x y))))

;;? AND ? and IGNORE
(deffun unify-without-occur-check (x y)
  (cond ((eq x y))
	((consp x)
	 (cond ((consp y)
		(and (unify-without-occur-check (car x) (car y))
		     (unify-without-occur-check (cdr x) (cdr y))))
	       ((%uvar-constant y x))))
	((consp y)
	 (%uvar-constant x y))
	((%uvar x y))))

;;? AND ? and PREVENT
(deffun unify-with-occur-check (x y)
  (cond ((eq x y))
	((consp x)
	 (cond ((consp y)
		(and (unify-with-occur-check (car x) (car y))
		     (unify-with-occur-check (cdr x) (cdr y))))
	       ((%uvar-constant-occur-check y x))))
	((consp y)
	 (%uvar-constant-occur-check x y))
        ((%uvar x y))))

;;? AND ? and HANDLE
;;Can't tail recurse due to WITH-CONS-BOUND-TO-CONS.
(defun unify-handle-circularity (x y)
  (cond ((eq x y))
	((consp x)
	 (cond ((consp y)
		(WITH-CONS-PARTS x
		  (WITH-CONS-PARTS y
		    (let ((first-x (first x))
			  (rest-x (rest1 x))
			  (first-y (first y))
			  (rest-y (rest1 y)))
		      (cond ((and (eq first-x first-y) (eq rest-x rest-y)))
			    (t (WITH-CONS-BOUND-TO-CONS x y
				 (and (unify-handle-circularity first-x first-y)
				      (unify-handle-circularity
					(%DEREFERENCE rest-x)
					(%DEREFERENCE rest-y))))))))))
	       ((%uvar-constant y x))))
	((consp y)
	 (%uvar-constant x y))
        ((%uvar x y))))

(defun install-circularity-mode-ignore ()
  (setf #'bind-cell-check 'bind-cell-without-occur-check)
  (setf #'unify 'unify-without-occur-check))

(defun install-circularity-mode-prevent ()
  (setf #'bind-cell-check 'bind-cell-with-occur-check)
  (setf #'unify 'unify-with-occur-check))

(defun install-circularity-mode-handle ()
  (setf #'bind-cell-check 'bind-cell-without-occur-check)
  (setf #'unify 'unify-handle-circularity))

(install-circularity-mode-ignore)

(deffun occur-check (x y)
  (cond ((consp y)
         (and (occur-check x (car y)) (occur-check x (cdr y))))
        ((typep y 'prolog-flavor)
         (multiple-value-bind (ordinary-term prolog-flavor-p)
             (send y ':ordinary-term)
         (and (not prolog-flavor-p) (occur-check x ordinary-term))))
        (t (neq x y))))

(defsubst occurs-in (x y) (not (occur-check x y)))
