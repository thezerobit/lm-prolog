;;; -*- Mode:LISP; Package:PROLOG; Base:10; Options:((WORLD SYSTEM)) -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;this file contains LM-Prolog predicates that are generally useful

(define-predicate same
  (:options
     (:documentation "unifies its arguments, if possible, or else fails.
 It works for any number of arguments. (SAME) is true.")
     (:argument-list (&rest terms)))
  ;;= should really do this but until I can compile it well its too expensive
  ((same ?x ?x . ?more)
   (same ?x . ?more))
  ((same ?))
  ((same)))

(define-predicate identical
  (:options
    (:documentation
	      "succeeds if its arguments are identical, otherwise fails.
 Two variables are identical only if they are the same variable or have
 been unifed.  Two constants are identical if they are EQUAL (in the Lisp sense).
 Two compound terms are identical, if their parts are identical.")
	    (:argument-list (&rest terms)))
  ((identical))
  ((identical ?))
  ((identical ?x ?y)
   (lisp-predicate (identical-p '?x '?y) ))
  ((identical ?x ?y ?z . ?more)
   (identical ?x ?y)
   (identical ?y ?z . ?more)))

(define-predicate not-identical
  (:options (:compile-method :open)
	    (:documentation
	      "succeeds if its arguments are NOT identical, otherwise fails.
 Two variables are identical only if they are the same variable or have
 been unifed.  Two constants are identical if they are EQUAL (in the Lisp sense).
 Two compound terms are identical, if their parts are identical.")
	    (:argument-list (x y)))
  ((not-identical ?X ?Y)
   (lisp-predicate (not (identical-p '?X '?Y)) )))

(define-predicate sum
  (:options (:compile-method :open)
	    (:documentation
	      "unifies SUM with the sum of +NUMBERS which must be numbers.")
	    (:argument-list (sum &rest +numbers)))
  ((sum ?sum . ?arguments)
   (lisp-value ?sum (apply #'+ '?arguments) )))

(define-predicate product
  (:options
    (:compile-method :open)
    (:documentation
      "unifies PRODUCT with the product of +NUMBERS which must be numbers.")
    (:argument-list (product &rest +numbers)))
  ((product ?product . ?arguments)
   (lisp-value ?product (apply #'* '?arguments) )))

(define-predicate difference
  (:options
    (:compile-method :open)
    (:argument-list (difference +x +y))
    (:documentation
      "unifies DIFFERNCE with the difference of +X and +Y which must be numbers."))
  ((difference ?difference ?x ?y)
   (lisp-value ?difference (- '?x '?y) )))

(define-predicate quotient
  (:options (:compile-method :open)
	    (:documentation
	      "unifies QUOTIENT with the quotient of +DIVIDEND and +DIVISOR which must be numbers.")
	    (:argument-list (quotient +dividend +divisor)))
  ((quotient ?quotient ?dividend ?divisor)
   (lisp-value ?quotient (quotient '?dividend '?divisor) )))


(define-predicate >
  (:options (:compile-method :open)
	    (:documentation
	      "succeeds if its arguments are in strictly descending order.
 All the arguments must be numbers.")
	    (:argument-list (&rest +numbers)))
  ((>))
  ((> ?x . ?arguments) (lisp-predicate (lexpr-funcall #'> '?x '?arguments)
				       )))

(define-predicate <
  (:options (:compile-method :open)
	    (:documentation
	      "succeeds if its arguments are in strictly ascending order.
 All the arguments must be numbers.")
	    (:argument-list (&rest +?numbers)))
  ((<))
  ((< ?x . ?arguments) (lisp-predicate (lexpr-funcall #'< '?x '?arguments)
				       )))

(define-predicate 
  (:options (:compile-method :open)
	    (:documentation "succeeds if its arguments are in descending order.
 All the arguments must be numbers.")
	    (:argument-list (&rest +numbers)))
  (())
  (( ?x . ?arguments) (lisp-predicate (lexpr-funcall #' '?x '?arguments)
				       )))

(define-predicate 
  (:options (:compile-method :open)
	    (:documentation "succeeds if its arguments are in ascending order.
 All the arguments must be numbers.")
	    (:argument-list (&rest +numbers)))
  (())
  (( ?x . ?arguments) (lisp-predicate (lexpr-funcall #' '?x '?arguments)
				       )))


(define-predicate >=
  (:options (:compile-method :open)
	    (:documentation "succeeds if its arguments are in descending order.
 All the arguments must be numbers.")
	    (:argument-list (&rest +numbers)))
  ((>=))
  ((>= ?x . ?arguments) (lisp-predicate (lexpr-funcall #'>= '?x '?arguments)
				       )))

(define-predicate <=
  (:options (:compile-method :open)
	    (:documentation "succeeds if its arguments are in ascending order.
 All the arguments must be numbers.")
	    (:argument-list (&rest +numbers)))
  ((<=))
  ((<= ?x . ?arguments) (lisp-predicate (lexpr-funcall #'<= '?x '?arguments)
				       )))

;;(define-predicate atomic (:options (:compile-method :open))
;;  ((atomic ?form) (lisp-type ?T ?form) (not-= ?T :list)))

(define-predicate variable
  (:options (:compile-method :open)
	    (:documentation "succeeds only if its argument is unbound.")
	    (:argument-list (term)))
  ((variable ?X) (lisp-predicate (unbound-variable-p '?X) )))

(define-predicate not-variable
  (:options (:compile-method :open)
	    (:documentation "succeeds only if its argument is bound.")
	    (:argument-list (term)))
  ((not-variable ?X)
   (lisp-predicate (not (unbound-variable-p '?x)) )))

(define-predicate atomic
  (:options (:compile-method :open)
	    (:documentation
	      "succeeds only if its argument neither a list nor unbound.")
	    (:argument-list (term)))
  ((atomic ?form) (not-variable ?form) (not-= ?form (? . ?))))

(define-predicate symbol ;;this is called ATOM in Edinburgh Prolog
  (:options (:compile-method :open)
	    (:documentation "succeeds only if its argument is a symbol.")
	    (:argument-list (term)))
  ((symbol ?form) (lisp-type symbol ?form)))

(define-predicate number
  (:options (:compile-method :open)
	    (:documentation
	      "succeeds only if its argument is a number.")
	    (:argument-list (term)))
  ((number ?term) (lisp-predicate (numberp '?term) :invoke)))

(define-predicate finite
  (:options (:compile-method :open)
	    (:argument-list (term))
	    (:documentation "holds only if there are no cycles within TERM."))
  ((finite ?term) (lisp-predicate (not (circular-p '?term)) )))

(define-predicate infinite
  (:options (:compile-method open)
	    (:argument-list (term))
	    (:documentation "holds only if there are cycles within TERM."))
  ((infinite ?term) (lisp-predicate (circular-p '?term) )))

;;;the following were never useful

;(define-predicate first (:options (:compile-method :open))
;  ((first ?x (?x . ?))))

;(define-predicate second (:options (:compile-method :open))
;  ((second ?x (? ?x . ?))))

;(define-predicate third (:options (:compile-method :open))
;  ((third ?x (? ? ?x . ?))))

;(define-predicate fourth (:options (:compile-method :open))
;  ((fourth ?x (? ? ? ?x . ?))))

;(define-predicate rest (:options (:compile-method :open))
;  ((rest ?x (? . ?x))))

;(define-predicate list (:options (:compile-method :open))
;  ((list ?list . ?list)))

(define-predicate tyi
  (:options (:compile-method :open)
	    (:documentation
	      "unifies its first argument with the ascii of the next character read.
 The second argument is optional and specifies the stream to read from.
 The third argument is optional and specifies the end of file option.")
	    (:argument-list (ascii &optional +stream +eof-option)))
  ((tyi ?ascii . ?arguments)
   (lisp-value ?ascii (apply #'tyi '?arguments) )))

(define-predicate tyo
  (:options (:compile-method :open)
	    (:documentation
	      "outputs the first argument to stream and always succeeds.
 The second are argument is optional and specifies the stream to print to.")
	    (:argument-list (+ascii &optional +stream)))
  ((tyo . ?arguments)
   (lisp-command (apply #'tyo '?arguments) )))

(define-predicate read
  (:options (:documentation "unifies its first argument with the next term read.
 The second argument is optional and specifies the stream to read from.
 The third argument is optional and specifies the end of file option.
 Any variables in the term read are local to the read.")
	    (:argument-list (term &optional +stream +eof-option)))
  ((read ?form . ?arguments)
   (lisp-value ?form
	       (parse-term (lexpr-funcall #'read '?arguments)) )))

(define-predicate global-read 
  (:options (:documentation "unifies its first argument with the next term read.
 The second argument is optional and specifies the stream to read from.
 The third argument is optional and specifies the end of file option.
 Any variables in the term read are shared by subsequent calls global-read.")
	    (:argument-list (term &optional +stream +eof-option)))
  ((global-read ?form . ?arguments)
   (lisp-value ?form
	       (parse-term (lexpr-funcall #'read '?arguments) t) )))

(define-predicate princ
  (:options (:documentation
	      "Applies Lisp function PRINC on TERM and +STREAM and succeeds.")
	    (:argument-list (term &optional +stream)))
  ((princ . ?arguments)
   (lisp-command (apply 'princ '?arguments) :dont-invoke)))

(define-predicate prin1
  (:options (:documentation
	      "Applies Lisp function PRIN1 on TERM and +STREAM and succeeds.")
	    (:argument-list (term &optional +stream)))
  ((prin1 . ?arguments)
   (lisp-command (apply 'prin1 '?arguments) :dont-invoke)))

(define-predicate prin1-then-space
  (:options (:documentation
	      "Applies Lisp function PRIN1-THEN-SPACE on TERM and +STREAM and succeeds.")
	    (:argument-list (term &optional +stream)))
  ((prin1-then-space . ?arguments)
   (lisp-command (apply 'prin1-then-space '?arguments) :dont-invoke)))

(define-predicate print
  (:options (:documentation
	      "Applies Lisp function PRINT on TERM and +STREAM and succeeds.")
	    (:argument-list (term &optional +stream)))
  ((print . ?arguments)
   (lisp-command (apply 'print '?arguments) :dont-invoke)))

(define-predicate pprint
  (:options (:documentation
	      "Applies Lisp function PPRINT on TERM and +STREAM and succeeds.")
	    (:argument-list (term &optional +stream)))
  ((pprint . ?arguments)
   (lisp-command (apply 'pprint '?arguments) :dont-invoke)))

(define-predicate write
  (:options (:documentation
	      "Applies Lisp function WRITE on TERM and +STREAM and succeeds.")
	    (:argument-list (term &optional +stream)))
  ((write . ?arguments)
   (lisp-command (apply 'write '?arguments) :dont-invoke)))

(define-predicate open-file
  (:options (:documentation
	      "unifies STREAM with the stream produced by opening +FILE-NAME.
 More arguments to the OPEN function are given by additional optional arguments.")
	    (:argument-list (stream +file-name &rest open-arguments)))
  ((open-file ?stream . ?arguments)
   ;;this will close the stream upon backtracking or abnormal return
   (lisp-value ?stream (lexpr-funcall #'open '?arguments))
   (unwind-protect (true) (lisp-command (close '?stream)))))

(define-predicate format
  (:options
    (:argument-list (+stream +control-string &rest +arguments))
    (:documentation
      "outputs to the +stream controlled by the +control-string.
 The additional arguments are arguments to the formatting control string.

 See deocumentation of the Lisp function format.
 "))
  ((format ?stream ?control-string . ?arguments)
   (lisp-command (lexpr-funcall #'format '?stream '?control-string '?arguments)
		 :dont-invoke)))

(define-predicate y-or-n
  (:options
     (:documentation
       "applies FORMAT to its arguments, then asks the user (Y or N) whether to succeed.")
     (:argument-list (+format-control-string &rest +format-arguments)))
  ((y-or-n ?format-control-string . ?format-arguments)
   (format t ?format-control-string . ?format-arguments)
   (lisp-predicate (y-or-n-p))))

(define-predicate error
  (:options
     (:documentation
       "signals a non-proceedable error")
     (:argument-list (+signal-name &rest +signal-name-arguments)))
  ((error ?signal-name . ?signal-name-arguments)
   (lisp-command (lexpr-funcall 'prolog-ferror '?signal-name '?signal-name-arguments)
		 )))

(putprop (definition-prover (current-definition 'error)) t ':error-reporter)

(define-predicate load
  (:options (:documentation "loads a file using Lisp's load.  Always succeeds."))
  ((load . ?arguments)
   (lisp-command (apply #'load '?arguments))))

(define-predicate compile			;8
  (:options (:argument-list (predicator &optional world worlds))
	    (:documentation "compiles PREDICATOR in WORLD.
 If WORLD isn't given then an element of WORLDS which defaults to the universe.
 Succeeds for each PREDICATOR found."))
  ((compile ?predicator)
   (compile ?predicator ?))
  ((compile ?predicator ?world)
   (compile ?predicator ?world ?))
  ((compile ?predicator ?world ?worlds)
   (predicator ?predicator ?world ?worlds)
   (lisp-command (compile-definition (definition-in-world '?predicator '?world))
		 )))

(define-predicate compile-file			;8
  (:options
     (:argument-list (+file-name &rest +arguments))
     #-symbolics
     (:documentation "compiles +FILE-NAME using Lisp's QC-FILE.  Always succeeds.")
     #+symbolics
     (:documentation "compiles +FILE-NAME using Lisp's COMPILER:COMPILE-FILE.  Always succeeds."))
  ((compile-file . ?arguments)
   (lisp-command (apply #-symbolics #'qc-file
			#+symbolics #'compiler:compile-file '?arguments)
		 )))

(define-predicate append
  (:options (:argument-list (appended &rest parts))
	    (:documentation
	      "succeeds if APPENDED unifies with the result of appending PARTS."))
  ((append ()))
  ((append ?x ?x))			   ;7.12
  ((append ?x () ?y . ?z)
   (append ?x ?y . ?z))
  ((append (?first . ?rest-x-and-y) (?first . ?rest-x) ?y . ?z)
   (append ?rest-x-and-y ?rest-x ?y . ?z)))

(define-predicate reverse
  (:options (:argument-list (reversed list &optional back))
	    (:documentation "succeeds if REVERSED appended with BACK unifies with the reversal of LIST.
 Note that while this works with REVERSED given and LIST unknown it will run slower."))
  ((reverse ?reversed () ?reversed))
  ((reverse ?reversed (?first . ?rest) ?reversed-so-far)
   (reverse ?reversed ?rest (?first . ?reversed-so-far)))
  ((reverse ?reversed ?x)
   (cases ((variable ?reversed) (reverse ?reversed ?x ()))
	  ((prove-once (reverse ?reversed ?x ()))))))


(define-predicate length
  (:options (:argument-list (length list &optional end-of-list))
	    (:documentation
	      "succeeds if LENGTH is the length of the LIST minus END-OF-LIST."))
  ((length 0 ?left ?left))
  ((length ?n (? . ?rest) ?left)
   (length ?n-1 ?rest ?left)
   (sum ?n ?n-1 1))
  ((length ?n ?list)
   (cases ((variable ?n) (length ?n ?list ()))
	  ((prove-once (length ?n ?list ()))))))

(define-predicate nth
  (:options
     (:argument-list (item index list &optional ignore))
     (:documentation "succeeds if ITEM unifies with the INDEXth element of LIST."))
  ((nth ?first 0 (?first . ?) ?))
  ((nth ?nth ?n (? . ?rest) ?ignore)
   (nth ?nth ?n-1 ?rest ?ignore)
   (sum ?n ?n-1 1))
  ((nth ?item ?index ?list)
   (cases ((variable ?index) (nth ?item ?index ?list ignore))
	  ((prove-once (nth ?item ?index ?list ignore))))))

(define-predicate substitute
  (:options (:argument-list
	      (substituted old new form &optional (+test-predicate identical)))
	    (:documentation
	      "succeeds if SUBSTITUTED is the result of replacing all components X
 of FORM for which (+TEST-PREDICATE X OLD) holds with NEW."))
  ((substitute ?substituted ?old ?new ?form ?test-predicate)
   (cases ((prove-once (?test-predicate ?form ?old)) (= ?substituted ?new))
	  ((and (not-variable ?form) (= ?form (?first . ?rest)))
	   (substitute ?first-substituted ?old ?new ?first ?test-predicate)
	   (substitute ?rest-substituted ?old ?new ?rest ?test-predicate)
	   (= ?substituted (?first-substituted . ?rest-substituted)))
	  ((= ?form ?substituted))))
  ((substitute ?substituted ?old ?new ?form)
   (substitute ?substituted ?old ?new ?form identical)))

(define-predicate member
  (:options (:argument-list (element list))
	    (:documentation "succeeds if ELEMENT is a member of LIST."))
  ((member ?x (?x . ?)))
  ((member ?x (? . ?y)) (member ?x ?y)))

(define-predicate delete
  (:options (:argument-list (left element list))
	    (:documentation "succeeds if LEFT is LIST with ELEMENT spliced out."))
  ((delete ?all ?x (?x . ?all)))
  ((delete (?x . ?some) ?y (?x . ?all))
   (delete ?some ?y ?all)))

(define-predicate remove
  (:options (:argument-list (left element +list))
	    (:documentation
	      "succeeds if LEFT is those elements of +LIST which do not match ELEMENT."))
  ((remove ?left ?element ?list)
   (bag-of ?left ?x (member ?x ?list) (not-= ?x ?element))))

(define-predicate intersection
  (:options (:argument-list (intersection &rest +lists))
	    (:documentation "succeeds if INTERSECTION contains only those elements common to each of the +LISTS."))
  ((intersection () () . ?))
  ((intersection ?intersection (?first . ?rest) . ?lists)
   (cases ((member-of-each ?first . ?lists)
	   (intersection ?rest-intersection ?rest . ?lists)
	   (= ?intersection (?first . ?rest-intersection)))
	  ((intersection ?intersection ?rest . ?lists))))
  ((intersection ())))

(define-predicate member-of-each
  ((member-of-each ?))
  ((member-of-each ?x ?list . ?more-lists)
   (member ?x ?list)
   (member-of-each ?x . ?more-lists)))

(define-predicate union
  (:options (:argument-list (union &rest +lists))
	    (:documentation "succeeds if UNION contains only those elements occuring in at least one of +LISTS."))
  ((union ?union . ?lists)
   (union-1 ?union () . ?lists)))

(define-predicate union-1
  ((union-1 ?union ?union))
  ((union-1 ?union ?so-far () . ?lists)
   (union-1 ?union ?so-far . ?lists))
  ((union-1 ?union ?so-far (?first . ?rest) . ?lists)
   (cases ((member ?first ?so-far)
	   (union-1 ?union ?so-far ?rest . ?lists))
	  ((union-1 ?union (?first . ?so-far) ?rest . ?lists)))))

(define-predicate partition-for-sorting
  (:options (:argument-list (+list +element +relation -smaller -bigger)))
  ((partition-for-sorting (?first . ?rest) ?x ?relation ?smaller ?bigger)
   (cases ((?relation ?x ?first)
	   (= ?smaller (?first . ?smaller-1))
	   (partition-for-sorting ?rest ?x ?relation ?smaller-1 ?bigger))
	  ((= ?bigger (?first . ?bigger-1))
	   (partition-for-sorting ?rest ?x ?relation ?smaller ?bigger-1))))
  ((partition-for-sorting () ? ? () ())))

(define-predicate sort
  (:options (:deterministic :always)
	    (:argument-list (sorted +unsorted +predicator &optional so-far))
	    (:documentation "SORTED is +UNSORTED sorted by the relation named by +PREDICATOR."))
  ((sort ?sorted ?list ?predicator) (sort ?sorted ?list ?predicator ()))
  ((sort ?sorted (?first . ?rest) ?predicator ?so-far)
   (partition-for-sorting ?rest ?first ?predicator ?smaller ?bigger)
   (sort ?smaller-sorted ?smaller ?predicator ?so-far)
   (sort ?sorted ?bigger ?predicator (?first . ?smaller-sorted)))
  ((sort ?sorted () ? ?sorted)))

;(define-predicate generate-unique-name
;  ((generate-unique-name ?name) (generate-name ?name unique-name)))

(define-predicate generate-name
  (:options (:argument-list (symbol +name &optional +name2))
	    (:documentation "generates a unique interned symbol whose print name begins with
 +NAME or +NAME-+NAME2"))
  ((generate-name ?new-name ?old-name)
   (lisp-value ?new-name (generate-interned-symbol '?old-name)))
  ((generate-name ?new-name ?name-1 ?name-2)
   (lisp-value ?both-names (prolog-intern "~a-~a" '?name-1 '?name-2))
   (generate-name ?new-name ?both-names)))

(define-predicate generate-symbol
  (:options (:argument-list (symbol +name))
	    (:documentation "generates a unique un-interned symbol whose print name begins with +NAME.
 Note that if the ?SYMBOL is to be asserted in the database then use generate-permanent-symbol."))
  ((generate-symbol ?new-symbol ?name)
   (lisp-value ?new-symbol (create-symbol '?name))))

(define-predicate generate-permanent-symbol
  (:options (:argument-list (symbol +name))
	    (:documentation "generates a unique un-interned symbol whose print name begins with +NAME.
 Note that if the ?SYMBOL is not to be asserted in the database then generate-symbol is preferred."))
  ((generate-permanent-symbol ?new-symbol ?name)
   (lisp-value ?new-symbol (create-permanent-symbol '?name))))

(define-predicate time-and-print
  (:options (:argument-list (+predication &optional +label))
	    (:documentation "proves its first argument and prints timing info.
 Can backtrack."))
  ((time-and-print ?predication)
   (time-and-print ?predication "It"))
  ((time-and-print ?predication ?label)
   (time ?timing ?predication)
   (either (not-variable ?label) (= ?label "It"))
   (print-timing ?timing ?label)))

#-3600
(define-predicate print-timing
  ((print-timing (?run-time ?paging-time) ?label)
   (lisp-value ?run-time-seconds (* '?run-time 1.0e-6))
   (lisp-value ?paging-time-seconds (* '?paging-time 1.0e-6))
   (format t "~%~a took ~4f seconds (plus ~4f seconds paging)"
	   ?label ?run-time-seconds ?paging-time-seconds)))

#+3600
(define-predicate print-timing
  ((print-timing (?run-time ?) ?label)
   (lisp-value ?run-time-seconds (* '?run-time 1.0e-6))
   (format t "~%~a took ~4f seconds (including paging time)"
	   ?label ?run-time-seconds)))

(define-predicate no-clock-interrupts
  ((no-clock-interrupts)
   (lisp-value ?interrupts (si:sb-on))
   (lisp-command
     (si:sb-on (remq ':clock (si:sb-on))) ;;turn off clock interrupts
     )
   (unwind-protect (true) (lisp-command (si:sb-on '?interrupts)))))

(declare (special *cpubeg* *dskbeg*))

(define-predicate time
  (:options (:argument-list (cpu+dsk +predication))
	    (:documentation "unifies CPU and DISK with the cpu and disk
 time consumption for finding a proof of +PREDICATION.  It backtracks in the
 same way as TIME-AND-PRINT.  CPU and DISK will not
 contain accumulated values but just the time to find the first proof, the
 next proof, or to ultimately fail."))
  ((time (?cpu ?dsk) ?predication)
   (lisp-command
     (progn
       #-3600 (setq *dskbeg* (read-meter 'sys:%disk-wait-time))
       (setq *cpubeg* (time:microsecond-time)))
     )
   (or ?predication (true))
   (unwind-protect
     (lisp-command
       (let ((cpuend (time:microsecond-time))
	     #-3600 (dskend (read-meter 'sys:%disk-wait-time))
	     )
	 (unify '?dsk #-3600 (- dskend *dskbeg*)
		      #+3600 0)
	 (unify '?cpu (- cpuend *cpubeg* '?dsk)))
       )
     (lisp-command
       (progn #-3600 (setq *dskbeg* (read-meter 'sys:%disk-wait-time))
	      (setq *cpubeg* (time:microsecond-time)))
       ))))

#-3600
(define-predicate meter
  (:options (:documentation "proves its first argument with metering on.
 Meter analysis is saved in Zwei buffer Meter Information"))
  #-(or 3600 lambda)				;This meters every stack group.
  ((meter ?predication)
   (no-clock-interrupts)
   (unwind-protect (lisp-command (progn (meter:reset)
					(meter:enable t)
					(setq meter:%meter-micro-enables #o14))
				 )
		   (lisp-command (progn (setq meter:%meter-micro-enables #o0)
					(meter:disable))
				 ))
   (or ?predication (true))
   (unwind-protect
     (lisp-command
       (progn (setq meter:%meter-micro-enables #o0)
	      (meter:disable)
	      (meter:analyze ':buffer "Meter Information")
	      (format (zwei:interval-stream
			(zwei:find-buffer-named "Meter Information" t))
		      "~%~%Metering of ~s.~%" '?predication))
       )
     (lisp-command (progn (meter:reset)
			  (meter:enable t)
			  (setq meter:%meter-micro-enables #o14))
		   )))
  #+3600					;This doesnt meter.
  ((meter ?)
   (format t "Metering is not yet available on 3600s"))
  #+lambda					;This meters the current stack group.
  ((meter ?predication)
   (no-clock-interrupts)
   (unwind-protect (lisp-command (progn (meter:reset)
					(meter:enable si:%current-stack-group)
					(compiler:%set-meter-enables #o17)
					(meter:do-stack-group-switch))
				 )
		   (lisp-command (progn (compiler:%set-meter-enables #o0)
					(meter:disable)
				 )))
   (or ?predication (true))
   (unwind-protect
     (lisp-command
       (progn (compiler:%set-meter-enables #o0)
	      (meter:disable)
	      (meter:analyze ':buffer "Meter Information")
	      (format (zwei:interval-stream
			(zwei:find-buffer-named "Meter Information" t))
		      "~%~%Metering of ~s.~%" '?predication))
       )
     (lisp-command (progn (meter:reset)
			  (meter:enable si:%current-stack-group)
			  (compiler:%set-meter-enables #o17)
			  (meter:do-stack-group-switch))
		   ))))

;;; For lambda-expressions...

(define-predicate lambda
  (:options
    (:argument-list (-abstraction +globals +lambda-list &rest +body))
    (:documentation "unifies ?ABSTRACTION with a lambda expression
 which is like a nameless clause ((P . ?LAMBDA-LIST) . ?BODY).
 A call (?ABSTRACTION . ?ARGUMENT-LIST) will succeed if 
 (= ?LAMBDA-LIST ?ARGUMENT-LIST) and (AND . ?BODY) succeed.
 +GLOBALS is a list of variables which are not to be treated
 as local to the lambda expression."))
  ((lambda ?abstraction ?globals ?lambda-list . ?body)
   (lisp-value ?abstraction (make-lambda-template '?globals '?lambda-list '?body))))

