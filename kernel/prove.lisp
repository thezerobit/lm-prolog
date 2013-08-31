;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;This contains the theorem prover of LM-Prolog's interpreter.

;;This speeds up the interpreter by about 5% 
;;(since prove-conjunction isn't called with an empty list of predications).
(defsubst prove-conjunction-if-need-be (predications continuation)
  (cond ((null predications) (invoke continuation))
        (t (prove-conjunction predications continuation))))

(DEFSUBST TRY-FIRST (clauses TRY-FIRST-continuation arguments)
  (let ((templates
	  ;;for Symbolics sending the message is faster
	  #-3600 (symeval-in-instance (first clauses) 'prover)
	  #+3600 (send (first clauses) ':prover)))
    (COND ((ATOM TEMPLATES) (FUNCALL TEMPLATES TRY-FIRST-continuation arguments))
	  ((%unify-term-with-template arguments (first templates))
	   (let ((body (%construct (rest1 templates))))
	     (prove-conjunction-if-need-be body TRY-FIRST-continuation))))))


(deffsubst try-each (clauses try-each-continuation arguments mark)
  (cond ((NULL (REST1 CLAUSES))
	 ;;enables tail-recursion in the last clause
	 (TRY-FIRST clauses try-each-continuation arguments))
	((TRY-FIRST clauses try-each-continuation arguments))
	(t (untrail mark)
	   (try-each (rest1 clauses) try-each-continuation arguments mark))))

(defsubst prove (predication interpreter-slot continuation)
  (let ((prover (interpreter-slot-prover interpreter-slot))
	(CLAUSES (interpreter-slot-clauses interpreter-slot)))
    (cond ((null prover)
	   (COND (CLAUSES
		  (try-each CLAUSES continuation (rest1 predication) *trail*))))
          (t (lexpr-funcall prover continuation (rest1 predication))))))

#+lexical
(defun prove-1 (predication interpreter-slot continuation)
  (let ((prover (interpreter-slot-prover interpreter-slot))
	(CLAUSES (interpreter-slot-clauses interpreter-slot)))
    (cond ((null prover)
	   (COND (CLAUSES
		  (try-each CLAUSES continuation (rest1 predication) *trail*))))
          (t (lexpr-funcall prover continuation (rest1 predication))))))

(deffun prove-conjunction (predications continuation)
  (let* ((predication (first predications))
	 (predicator (lisp-form-1 (first predication) ':dont-invoke)))
    (cond ((symbolp predicator)
	   (let ((interpreter-slot
		   (definition-interpreter-slot (current-definition predicator))))
	     (cond ((interpreter-slot-deterministic interpreter-slot)
		    (cond ((prove predication interpreter-slot (continuation (true)))
			   (prove-conjunction-if-need-be (rest1 predications)
							 continuation))))
		   
		   ((null (rest1 predications))
		    (prove predication interpreter-slot continuation))
		   (t (let ((continuation-1
			      (continuation (funcall #'prove-conjunction
						     (rest1 predications)
						     continuation))))
			(#-lexical prove #+lexical prove-1
			 predication interpreter-slot continuation-1))))))
	  (t (send predicator ':resolve-cont
		   (cond ((rest1 predications)
			  (continuation (funcall #'prove-conjunction (rest1 predications) continuation)))
			 (t continuation))
		   (rest1 predication))))))

(defvar *cut-tag* 'top-level-cut-tag)

(defun invoke-continuation (continuation *cut-tag*)
  (invoke continuation))


;;Begin finer-grained indexing.
(deffun try-indexed (indexes clauses1 continuation1 arguments1 mark1 &rest subsets)
  (cond ((null indexes)
	 (cond (subsets
		(try-subsets (car subsets) (cdr subsets) continuation1 arguments1 mark1))
	       (t
		(try-each clauses1 continuation1 arguments1 mark1))))
	(t (let* ((index (car indexes))
		  (key (funcall (index-key-finder index) arguments1)))
	     (cond ((value-cell-p key)
		    (lexpr-funcall 'try-indexed (cdr indexes)
				   clauses1 continuation1 arguments1 mark1 subsets))
		   (t (let ((some-clauses (gethash key (index-table index))))
			(cond (some-clauses
			       (lexpr-funcall 'try-indexed (cdr indexes)
					      clauses1 continuation1 arguments1 mark1
					      (cons-by-length some-clauses
							      (length some-clauses)
							      subsets)))))))))))

(deffun try-subsets (clauses subsets continuation arguments mark)
  (cond ((and (every subsets #'(lambda (subset) (memq (car clauses) subset)))
	      (try-first clauses continuation arguments)))
	((cdr clauses)
	 (untrail mark)
	 (try-subsets (cdr clauses) subsets continuation arguments mark))))

(defun cons-by-length (x l list)
  (cond ((null list) (prolog-list x))
	((> l (length (car list)))
	 (prolog-cons (car list) (cons-by-length x l (cdr list))))
	(t (prolog-cons x list))))
;;Begin finer-grained indexing.
