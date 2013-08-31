;;; -*- Mode: Lisp; Package: Puser; Base: 10.; Options: ((World Clock)); -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;A clock or watch in LM-Prolog using Eager Bags and stream Turtle graphics.

(define-predicate clock
  ((clock ?size)
   (product ?hour-hand-size .6 ?size)
   (product ?minute-hand-size .75 ?size)
   (product ?second-hand-size .9 ?size)
   (turtle-stream ((:circle ?size) . ?s) ?s)
   (eager-hand hours ?hour-hand-size ?)
   (eager-hand minutes ?minute-hand-size ?)
   (eager-hand seconds ?second-hand-size ?)))

(define-predicate eager-hand
  ((eager-hand ?time-unit ?size ?ignore)
   (prolog:eager-bag-of ?ignore ? (hand ?time-unit ?size))))

(define-predicate hand
  ((hand ?time-unit ?size)
   (repeat)
   (hand-angle ?angle ?time-unit)
   (turtle-stream-concurrent ((:placeturtle 0 0 ?angle) (:forward ?size) . ?s) ?s)
   (prolog:await (cannot-prove (hand-angle ?angle ?time-unit)))))

(define-predicate hand-angle
  ((hand-angle ?angle seconds)
   (the-times (?seconds . ?))
   (product ?angle ?seconds 6))
  ((hand-angle ?angle minutes)
   (the-times (? ?minutes . ?))
   (product ?angle ?minutes 6))
  ((hand-angle ?angle hours)
   (the-times (? ?minutes ?24-hours . ?))
   (lisp-value ?12-hours (remainder ?24-hours 12))
   (product ?minutes-add-on ?minutes .5)
   (product ?hour-angle ?12-hours 30)
   (sum ?angle ?hour-angle ?minutes-add-on)))
  
(define-predicate the-times
  ((the-times ?times)
   ;;?times is
   ;;seconds, minutes, hours, date, month, year, day-of-week, day-light-savings-p
   (lisp-value ?times (multiple-value-list (time:get-time)) :dont-invoke)))


