;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; Options: ((World System)); -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


(define-predicate ask-about (:options (:lisp-macro-name ask-about))
  ((ask-about ?predicate-name)
   (option (:world ?world))
   (ask-about ?predicate-name ?world))
  ((ask-about ?predicate-name ?world)
   (generate-name ?internal-predicate-name ?predicate-name)
   (generate-name ?negative-predicate-name not ?predicate-name)
   (define-predicate ?internal-predicate-name
     (:options (:type :dynamic) (:world ?world)))
   (define-predicate ?negative-predicate-name
     (:options (:type :dynamic) (:world ?world)))
   (define-predicate ?predicate-name (:options (:world ?world))
     ((?predicate-name . ?arguments)
      (comment "This asks the user and remembers the answers in"
               ?internal-predicate-name)
      (ask-user-if-necessary ?predicate-name ?arguments ?world
                             ?internal-predicate-name ?negative-predicate-name)))))

(define-predicate ask-user-if-necessary
  ((ask-user-if-necessary ?predicate-name ?arguments ?world
                          ?internal-predicate-name ?negative-predicate-name)
   (variables ?variables ?arguments)
   (cases ((= ?variables ())
           (either (?internal-predicate-name . ?arguments)
                   (ask-user ?predicate-name ?arguments ?variables ?world
                             ?internal-predicate-name ?negative-predicate-name)))
          ((or (?internal-predicate-name . ?arguments)
               (ask-user ?predicate-name ?arguments ?variables ?world
                         ?internal-predicate-name ?negative-predicate-name))))))

(define-predicate ask-user
  ((ask-user ?predicate-name ?arguments ?variables ?world
             ?internal-predicate-name ?negative-predicate-name)
   (cases ((and ;(close ?arguments)
		(?negative-predicate-name . ?arguments))
	   (fail))
          ((cases ((= ?variables ())
                   (y-or-n "~%Is ~S true? " (?predicate-name . ?arguments))
                   (assert ((?internal-predicate-name . ?arguments)) ?world))
                  ((= ?variables (?variable))
		   (can-prove
		     (= ?variable "?x")
		     (y-or-n "~%Is there an ?x such that ~A? "
			     (?predicate-name . ?arguments)))
                   (or (and (ask-binding ?variable "?x")
                            (assert ((?internal-predicate-name . ?arguments))
                                    ?world))
                       (ask-user ?predicate-name ?arguments (?variable) ?world
                                 ?internal-predicate-name
                                 ?negative-predicate-name)))
                  ((y-or-n "~%Are there ~S such that ~S? "
                           ?variables (?predicate-name . ?arguments))
                   (or (and (map ask-binding ?variables)
                            (assert ((?internal-predicate-name . ?arguments))
                                    ?world))
                       (ask-user ?predicate-name ?arguments ?variables ?world
                                 ?internal-predicate-name
                                 ?negative-predicate-name)))))
          ((either (= ?variables ())
		   (y-or-n "~%Should I assume that it is always false? "))
	   (with (assert ((?negative-predicate-name . ?arguments)) ?world)
                 (fail))))))

(define-predicate ask-binding
  ((ask-binding ?variable) (ask-binding ?variable ?variable))
  ((ask-binding ?variable ?name)
   (format t "~%~A = " ?name)
   (read ?variable)))
