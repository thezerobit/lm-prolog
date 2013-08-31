;;; -*- Mode: Lisp; Package: Prolog; Base: 10.; Options: ((world arrays)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.

;;This file is an LM-Prolog implementation of arrays, 
;;Inspired by a proposal by E. Shapiro, written by Ken Kahn after
;;discussions with Lars-Henrik Eriksson, Manny Rayner, and Mats Carlsson

;;the idea is that there are 3 predicates, 
;;ARRAY-IS, ARRAY-ELEMENT, and ARRAY-DIFFERENCE which could be written in
;;Pure Prolog, but behind the scenes are using arrays both for their indexing
;;and their mutability


(comment
(define-predicate test-array
  ((test-array ?5 ?old-5 ?bar ?x ?not-foo ?not-x ?variable ?variable-3)
   (array-is ?a :(array (dimensions 10)))
   (array-difference ?a ?a-1 (foo 5))
   (array-element ?5 ?a-1 5)
   (array-element ?old-5 ?a 5)
   (array-difference ?a-1 ?a-2 (bar 5))
   (array-element ?bar ?a-2 5)
   (array-element ?x ?a-2 6)
   (array-element x ?a-2 6)
   (array-difference ?a-2 ?a-3 (not-x 6))
   (array-difference ?a ?a-11 (not-foo 5))
   (array-element ?bar ?a-2 5)
   (array-element ?old-5 ?a 5) 
   (array-element ?not-foo ?a-11 5)
   (array-element ?not-x ?a-3 6)
   (array-difference ?a-11 ? (foo 3))
   (array-element ?variable ?a-1 3)
   (array-difference ?a-1 ? (bar 4))
   (array-element ?variable-3 ?a-11 4))
  ((test-array ordinary)
   (test-array foo ?variable bar x not-foo not-x ?variable-2 ?variable-3)
   (variable ?variable)
   (variable ?variable-2)
   (variable ?variable-3))
  ((test-array initialized)
   (array-is ?a :(array (dimensions 10) (initial-value 27)))
   (array-difference ?a ?a-1 (foo 5))
   (array-element foo ?a-1 5)
   (array-element ?old-5 ?a 5)
   (array-difference ?a-1 ?a-2 (bar 5))
   (array-element bar ?a-2 5)
   (array-element 27 ?a-2 6)
   (array-difference ?a-2 ?a-3 (not-x 6))
   (array-difference ?a ?a-11 (not-foo 5))
   (array-element bar ?a-2 5)
   (array-element ?old-5 ?a 5)
   (array-element not-foo ?a-11 5)
   (array-element not-x ?a-3 6))
  ((test-array byte)
   (array-is ?a :(array (dimensions 10) (initial-value 7) (type 4-bit)))
   (array-difference ?a ?a-1 (foo 5))
   (array-element foo ?a-1 5)
   (array-element ?old-5 ?a 5)
   (array-difference ?a-1 ?a-2 (bar 5))
   (array-element bar ?a-2 5)
   (array-element 7 ?a-2 6)
   (array-difference ?a-2 ?a-3 (not-x 6))
   (array-difference ?a ?a-11 (not-foo 5))
   (array-element bar ?a-2 5)
   (array-element ?old-5 ?a 5)
   (array-element not-foo ?a-11 5)
   (array-element not-x ?a-3 6))
  ((test-array unify)
   (array-is ?a :(array (dimensions 10) (initial-value 27)))
   (array-difference ?a ?a-1 (foo 5))
   (array-difference ?a-1 ?a-2 ((bar) 5))
   (array-difference ?a-2 ?a-3 (not-x 6))
   (array-is ?b :(array (dimensions 10)))
   (array-difference ?b ?b-1 ((?bar) 5))
   (array-difference ?b-1 ?b-2 (not-x 6))
   (array-difference ?b-2 ? (foo 4))
   (array-difference ?a-2 ? (not-foo 4))
   (= ?a-3 ?b-2))
  ((test-array recent-only)
   (array-is ?a :(array (dimensions 10) (initial-value 0)
		  (usage recent-only deterministic)))
   (array-difference ?a ?a-1 (ett 1))
   (array-difference ?a-1 ?a-2 (two 2))
   (array-difference ?a-2 ?a-3 (three 3))
   (array-difference ?a-3 ?a-4 (one 1))
   (array-element ?ett ?a-1 1)
   (array-element ?one ?a-4 1)
   (= ?ett ?one) ;;logically wrong but then the usage declaration lied
   )
  ((test-array lispish)
   (array-is ?a :(array (dimensions 10) (initial-value 0) (usage lisp-like)))
   (array-difference ?a ?a-1 (ett 1))
   (array-difference ?a-1 ?a-2 (two 2))
   (array-difference ?a-2 ?a-3 (three 3))
   (array-difference ?a-3 ?a-4 (one 1))
   (array-element ?ett ?a-1 1)
   (array-element ?one ?a-4 1)
   (= ?ett ?one) ;;logically wrong but then the usage declaration lied
   ))
)

(eval-when (compile eval load)

(defflavor virtual-array (array location old-contents) (prolog-flavor)
  :initable-instance-variables)

(defflavor invalidated-virtual-array () (virtual-array))

(defflavor virtual-array-lisp-like () (virtual-array))

(defflavor virtual-array-lisp-like-no-trailing () (virtual-array-lisp-like))
)

(define-predicate array-is
  :(options
     (argument-list (array description))
     (documentation
       "creates an array meeting DESCRIPTION and unifies it with ARRAY.
 An array description is a cons of :array and a list of keywords
 paired with their values as follows:
 (:dimensions . <list-of-integers>)
 (:type <type>)
  ;; possible types are
  ;; :normal, :1-bit, :2-bit, :4-bit, :8-bit, :16-bit, :string and :fat-string
 (:initial-value <value>)
 (:usage . <list-of-declarations>)
  Only :dimensions is obligatory. :Type defaults to :normal.
  :Initial-value is by default 0, except for :normal arrays which are full of variables.
  The <list-of-declarations> may contain the flags :deterministic, :recent-only, 
  and :check.  Or it may contain only the flag :lisp-like.
  :deterministic declares that the array from its creation to its last update
  will be used deterministically.
  :recent-only declares that old versions of arrays are never referenced.
  :check tells the system to signal an error if either of the above declarations
  are violated.
  :lisp-like means that the array will be used :deterministic, :recent-only,
  and that indices are always ground and if the :type is not :normal that all the
  values will fit.
  These :usage declarations can significantly improve the efficiency of programs
  using arrays."))
  ((array-is ?array (:array . ?description))
   (cases ((variable ?array)
	   (cases ((variable ?description) ;7.12
		   (error :arg-error "either ARRAY or DESCRIPTION must be instantiated in IS"))
		  ((lisp-value ?array (virtual-array '?description)
			       ))))
	  ((lisp-predicate (typep '?array 'virtual-array) )
	   (lisp-value ?description
		       (let ((real-array (send '?array ':real-array)))
			 `((:dimensions ,@(array-dimensions real-array))
			   (:type ,(array-type real-array))))
		       )))))

(define-predicate array-element
  :(options
     (argument-list (value +array &rest indices))
     (documentation "binds VALUE with the +ARRAY element specified by INDICES."))
  ((array-element ?value ?array . ?indices)
   (lisp-value ?result (send '?array ':lookup '?indices) )
   (cases ((lisp-predicate (eq '?result 'bad-indices) )
	   ;;the above is ugly but this is time critical code
	   (valid-indices ?indices ?array)
	   (lisp-value ?value (send '?array ':lookup '?indices) ))
	 ((= ?result ?value)))))

(define-predicate valid-indices
  ((valid-indices ?indices ?array)
   (array-is ?array (:array . ?description))
   (member (:dimensions . ?dimensions) ?description)
   (map in-range ?indices ?dimensions)))

(define-predicate in-range
  ((in-range ?n ?too-high)
   (difference ?too-high-1 ?too-high 1)
   (or (= ?n ?too-high-1)
       (and (not-= ?too-high-1 0)
	    (in-range ?n ?too-high-1)))))

(define-predicate array-difference
  :(options
     (argument-list (+old-array new-array (new-value &rest indices)))
     (documentation
       "behaves as if it creates a new array NEW-ARRAY which differs from +OLD-ARRAlY
 in that the element indicated by INDICES is replaced by NEW-VALUE"))
  ((array-difference ?old-array ?new-array (?new-value . ?indices))
   (lisp-value ?result
	       (send '?old-array ':update '?new-value '?indices)
	       )
   (cases ((= ?result bad-indices)
	   (valid-indices ?indices ?old-array)
	   (lisp-value ?new-array
	       (send '?old-array ':update '?new-value '?indices)
	       ))
	 ((= ?result ?new-array)))))

(define-predicate array-difference-old-real
  :(options
     (argument-list (+old-array new-array (old-value new-value &rest indices)))
     (documentation
       "behaves as if it creates a new array NEW-ARRAY which differs from +OLD-ARRAY
 in that the element indicated by INDICES is replaced by NEW-VALUE"))
  ((array-difference-old-real ?old-array ?new-array (?new-value . ?indices))
   (lisp-value ?new-array
	       (make-instance-in-area
		 *prolog-work-area*
		 (type-of '?old-array)
		 ':array '?old-array
		 ':location '?indices
		 ':old-contents '?new-value)
	       )))

(defconst *lisp-array-types*
	  '((nil art-q)
	    (:normal art-q)
	    (:1-bit art-1b)
	    (:2-bit art-2b)
	    (:4-bit art-4b)
	    (:8-bit art-8b)
	    (:16-bit art-16b)
	    (:string art-string)
	    (:fat-string art-fat-string)))

(defsubst usage-update-methods (usage)
  (cond ((memq ':recent-only usage) ':re-use-old)
	((memq ':lisp-like usage) ':lisp-like)
	(t ':create-new)))

(defun virtual-array (description)
  ;;if this didn't use *prolog-work-area* then
  ;;one could assert a clause containing an array
  (let* ((array-type (or (second (assq ':type description)) ':normal))
	 (lisp-type (or (second (assq array-type *lisp-array-types*))
			(prolog-error ':bad-array-type-for-Prolog
				      "~s is not a valid Prolog array type"
				      array-type)))
	 (usage (rest1 (assq ':usage description)))
	 (initial-value
	   (cond ((second (assq ':initial-value description)))
		 ((eq lisp-type 'art-q) 'not-given)
		 (t 0)))
	 (real-array
	   (make-array (rest1 (assq ':dimensions description))
		       ':type lisp-type
		       ':initial-value initial-value
		       ':area *prolog-work-area*)))
    (and (eq initial-value 'not-given) (variablize-array real-array))
    (make-instance-in-area *prolog-work-area*
			   (virtual-array-name array-type
					       (usage-update-methods usage)
					       (not (memq ':deterministic usage))
					       (memq ':check usage))
			   ':array real-array
			   ':location nil)))

(defun variablize-array (array)
 ;;this "converts" the array if necessary to a one dimensional array
  (let ((dimensions (array-dimensions array)))
    (cond ((null (rest1 dimensions)) (variablize-array-1 array (first dimensions)))
	  (t (let ((dimension (apply 'times dimensions)))
	       (variablize-array-1 (make-array dimension ':displaced-to array)
				   dimension))))))

(deffun variablize-array-1 (array dimension &optional (index 0))
  (cond ((< index dimension)
	 ;;the following almost worked (sigh)
	 ;;(let ((location (aloc array index)))
	 ;;  (setf (contents location) location) ...)
	 (setf (aref array index) (%reference (%cell0)))
	 ;;the %reference here will screw things up if aset follows
	 ;;invisible pointers
	 (variablize-array-1 array dimension (add1 index)))))

(defconst *invalidated-array* (make-instance 'invalidated-virtual-array))

;;And now for flavor methods and subsidiaries.
(eval-when (compile eval load)
(defun virtual-array-name (array-type update-type trailing-p checking-p)
  (cond ((eq update-type ':lisp-like)
	 (cond (checking-p (format t "~&Warning can't check :lisp-like usage.")))
	 (cond (trailing-p 'virtual-array-lisp-like)
	       (t 'virtual-array-lisp-like-no-trailing)))
	(t (intern (format nil "VIRTUAL-ARRAY-~a-~a~a~a"
			  array-type update-type
			  (cond (trailing-p "")
				(t '-no-trailing))
			  (cond (checking-p '-checking)
				(t "")))
		   'prolog)))))

(eval-when (compile eval)
(defconst *array-types*
	  '((:1-bit 1)
	    (:2-bit 2)
	    (:4-bit 4)
	    (:8-bit 8)
	    (:16-bit 16)
	    (:string 8)
	    (:fat-string 16)
	    (:normal nil)))

(defconst *update-types* ':(create-new re-use-old lisp-like))

(defun virtual-array-type-definition
       (array-type size update-type trailing-p checking-p)
  (let ((name (virtual-array-name array-type update-type trailing-p checking-p)))
    `((defflavor ,name () (virtual-array))
      (defmethod (,name :update) (new-value indices)
	;;these size tests can be optimized away if declared so...
	,(cond ((null size)
		(array-update-body update-type trailing-p checking-p))
	       ((= size 1) ;;special case this one
		`(cond ((or (eql new-value 0) (eql new-value 1))
			,(array-update-body update-type trailing-p checking-p))
		       (t  ;;this is essentially an old-real update
			(make-instance-in-area
			  *prolog-work-area*
			  ',name
			  ':array self
			  ':location indices
			  ':old-contents new-value))))
	       (t (let ((max (sub1 (expt 2 size))))
		    `(cond ((and (fixp new-value)
				 (>= new-value 0)
				 (<= new-value ,max))
			    ,(array-update-body update-type trailing-p checking-p))
			   (t
			    (make-instance-in-area
			      *prolog-work-area*
			      ',name
			      ':array self
			      ':location indices
			      ':old-contents new-value))))))))))

(defun array-update-body (update-type trailing-p checking-p)
  (cond ((or (eq update-type ':create-new)
	     (and checking-p (eq update-type ':re-use-old)))
	 `(cond ((null location) ;;the end
		 (*catch 'bad-indices
		   (let ((current-contents
			   (condition-case ()
			       (lexpr-funcall #'aref array indices)
			     (error (*throw 'bad-indices 'bad-indices))))
			 (++array array)
			 (++self self))
		     ,@(cond (trailing-p
			      '((trail ;;undoes the following side-effects
				  (continuation
				    (send ++self ':restore-last-pointer
					  current-contents ++array)))))
			     (checking-p
			      '((trail
				  (continuation (send ++self ':invalidate))))))
		     (setq old-contents current-contents)
		     (setq location indices)
		     (lexpr-funcall #'aset new-value array indices)
		     (setq array
			   (make-instance-in-area *prolog-work-area*
						  (type-of self)
						  ':array array
						  ':location nil))
		     ,@(cond ((and checking-p (eq update-type ':re-use-old))
			      '((prog1 array
				       (setq array *invalidated-array*))))))))
		(T			   ;7.12
		 (LET ((NEW-ARRAY (send array ':update new-value indices)))
		   (COND ((SYMBOLP NEW-ARRAY) NEW-ARRAY)
			 ((EQUAL LOCATION INDICES) NEW-ARRAY)
			 (T (make-instance-in-area
			      *prolog-work-area*
			      (type-of self)
			      ':array NEW-ARRAY
			      ':location location
			      ':old-contents old-contents)))))))
	((eq update-type ':re-use-old)
	 (cond (trailing-p
		'(*catch 'bad-indices
		   (let ((current-contents
			   (condition-case ()
			       (lexpr-funcall #'aref array indices)
			     (error (*throw 'bad-indices 'bad-indices))))
			 (++array array))
		     (trail
		       (continuation
			 (lexpr-funcall #'aset current-contents ++array indices)))
		     (lexpr-funcall #'aset new-value array indices)
		     self)))
	       (t '(condition-case ()
		       (progn (lexpr-funcall #'aset new-value array indices)
			      self)
		     (error 'bad-indices)))))))

(defmacro define-all-array-types ()
  `(progn 'compile
	  ,@(mapcan
	      #'(lambda (array-type-pair)
		  (mapcan
		    #'(lambda (update-type)
			(append
			  (virtual-array-type-definition (first array-type-pair)
							 (second array-type-pair)
							 update-type
							 t
							 nil)
			  (virtual-array-type-definition (first array-type-pair)
							 (second array-type-pair)
							 update-type
							 nil
							 nil)
			  (virtual-array-type-definition (first array-type-pair)
							 (second array-type-pair)
							 update-type
							 t
							 t)
			  (virtual-array-type-definition (first array-type-pair)
							 (second array-type-pair)
							 update-type
							 nil
							 t)))
		    (remq ':lisp-like *update-types*)))
	      *array-types*)))
)

(define-all-array-types)

(defmethod (virtual-array-lisp-like :lookup) (indices)
   (lexpr-funcall #'aref array indices))

(defmethod (virtual-array-lisp-like :update) (new-value indices)
  (let ((current-contents (lexpr-funcall #'aref array indices))
	(++array array))
    (trail
      (continuation (lexpr-funcall #'aset current-contents ++array indices)))  
    (lexpr-funcall #'aset new-value array indices)
    self))

(defmethod (virtual-array-lisp-like-no-trailing :update) (new-value indices)
  (lexpr-funcall #'aset new-value array indices)
  self)

(defmethod (virtual-array :restore-last-pointer) (original-contents real-array)
  (setq array real-array)
  (lexpr-funcall #'aset original-contents real-array location)
  (setq location nil))

(defmethod (invalidated-virtual-array :update) (&rest ignore)
  (prolog-error ':invalidated-array
		"Can't update ~S since its declared to be obsolete."
		self))

(defmethod (invalidated-virtual-array :lookup) (&rest ignore)
  (prolog-error ':invalidated-array
		"Can't reference ~S since its declared to be obsolete."
		self))

(defmethod (invalidated-virtual-array :real-array) ()
  self)

(defmethod (virtual-array :invalidate) ()
  (setq array *invalidated-array*))

(defmethod (virtual-array :real-array) ()
  (cond ((null location) array)
	(t (send array ':real-array))))

(defmethod (virtual-array :lookup) (indices)
  (cond ((null location)
	 (condition-case ()
	     (lexpr-funcall #'aref array indices)
	   (error 'bad-indices)))
	((equal indices location) (%dereference old-contents))
	(t (send array ':lookup indices))))

(defmethod (virtual-array :ordinary-term) ()
  (values self t))

(defmethod (virtual-array :lisp-form) (mode)	;7.12
  (cond
;        ((eq mode ':dont-invoke) self)
	((and (null location) (neq mode ':copy) (neq mode ':copy-term)) array)	;RIGHT ?
	(t (let ((real-array (send self ':real-array)))
	     (cond ((typep real-array 'array)
		    (let* ((array-type (array-type real-array))
			   (copy (make-array (array-dimensions real-array)
					     ':type array-type
					     ':area *prolog-work-area*)))
		      (cond ((eq array-type 'art-q)
			    (let ((old-origin (ap-1-force real-array 0))
				  (new-origin (ap-1-force copy 0)))
			      (dotimes (i (array-active-length real-array))
				(selectq mode
				  (:copy-term
				   (rplacd new-origin (copy-term-1 (cdr old-origin))))
				  (t
				   (rplacd new-origin (lisp-form-1 (cdr old-origin) mode))))
				(setq old-origin
				      (%make-pointer-offset dtp-locative old-origin 1)
				      new-origin
				      (%make-pointer-offset dtp-locative new-origin 1)))))
			    (t (copy-array-contents real-array copy)))
		      (send self ':copy-into-real-array copy mode)
		      copy))
		   (t real-array))))))

(defmethod (virtual-array :copy-into-real-array) (new-array mode)	;7.12
  (cond ((not (null location))
	 (send array ':copy-into-real-array new-array mode)
	 (lexpr-funcall #'aset
			(selectq mode
			  (:copy-term (copy-term-1 (%dereference old-contents)))
			  (t (lisp-form-1 (%dereference old-contents) mode)))
			new-array
			location))))

(defmethod (virtual-array :copy) ()	   ;7.12
  (make-instance-in-area *prolog-work-area* (type-of self)
			 ':array (send self ':lisp-form ':copy-term) ':location nil))

(defmethod (virtual-array :unify) (other)
  (and (typep other 'virtual-array)
       (let* ((my-real-array (send self ':real-array))
	      (others-real-array (send other ':real-array))
	      (dimensions (array-dimensions my-real-array)))
	 (and (eq (array-type my-real-array) (array-type others-real-array))
	      (equal dimensions (array-dimensions others-real-array))
	      (unify-virtual-arrays self other my-real-array others-real-array
				    dimensions)))))

(defun unify-virtual-arrays (array-1 array-2 real-array-1 real-array-2 dimensions)
  (let* ((dimensions-reversed (rest1 (reverse dimensions)))
	 (exceptions-1 (send array-1 ':unify-exceptions array-2
			     dimensions-reversed nil)))
    (cond ((neq exceptions-1 'failed)
	   (let ((exceptions-2
		   (send array-2 ':unify-exceptions-with-real-array
			 real-array-1 dimensions-reversed exceptions-1)))
	     (cond ((neq exceptions-2 'failed)
		    (cond ((eq real-array-1 real-array-2))
			  (t (let ((size (apply 'times dimensions)))
			       (cond ((null (rest1 dimensions))
				      (unify-array-elements real-array-1
							    real-array-2
							    (sub1 size)
							    exceptions-2))
				     (t (unify-array-elements
					  (make-array size
						      ':displace-to real-array-1
						      ':area *prolog-work-area*)
					  (make-array size
						      ':displace-to real-array-2
						      ':area *prolog-work-area*)
					  (sub1 size)
					  exceptions-2)))))))))))))

(defmethod (virtual-array :unify-exceptions) (other dimensions exceptions-so-far)
  (cond ((null location) exceptions-so-far)
	(t (let ((index (one-dimensional-index location dimensions)))
	     (cond ((memq index exceptions-so-far)
		    (send array
			  ':unify-exceptions other dimensions exceptions-so-far))
		   ((unify (send other ':lookup location) old-contents)
		    (send array ':unify-exceptions other dimensions
			  (cons-in-area index exceptions-so-far
					*prolog-work-area*)))
		   (t 'failed))))))

(defmethod (virtual-array :unify-exceptions-with-real-array)
	   (real-array dimensions exceptions-so-far)
  (cond ((null location) exceptions-so-far)
	(t (let ((index (one-dimensional-index location dimensions)))
	     (cond ((memq index exceptions-so-far)
		    (send array
			  ':unify-exceptions-with-real-array
			  real-array dimensions exceptions-so-far))
		   ((unify (lexpr-funcall #'aref real-array location) old-contents)
		    (send self ':unify-exceptions-with-real-array
			  real-array dimensions
			  (cons-in-area index exceptions-so-far
					*prolog-work-area*)))
		   (t 'failed))))))

(deffun one-dimensional-index (indices dimensions)
  (cond ((null (rest1 indices)) (first indices))
	(t (plus (times (first indices) (apply 'times dimensions))
		 (one-dimensional-index (rest1 indices) (rest1 dimensions))))))

(deffun unify-array-elements (array-1 array-2 index exceptions)
  (cond ((>= index 0)
	 (cond ((memq index exceptions) ;;would it be better to use hashing???
		(unify-array-elements array-1 array-2 (sub1 index) exceptions))
	       ((unify (aref array-1 index) (aref array-2 index))
		(unify-array-elements array-1 array-2 (sub1 index) exceptions))))
	(t t)))

(comment ;;think more about whether this is so good
(advise parse-term-1 :around make-strings-mutable 0
  (cond ((stringp (first arglist))
	 (make-instance 'virtual-string-array
			':array (first arglist)
			':location nil))
	(t :do-it)))
)
