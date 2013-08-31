;;; -*- Mode: Lisp; Package: Prolog; Base: 10.; Options: ((World Parallel)); -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;some parallelism primitives using eager bags and sets in LM-Prolog

(define-predicate parallel-prove :(options (world parallel-prolog))
  ((parallel-prove (?predicator . ?arguments))
   (cases ((primitive-predicate ?predicator) (?predicator . ?arguments))
          ((clauses ?assertions (?predicator . ?arguments))
           (try-each ?assertions (?predicator . ?arguments))))))

(define-predicate try-each :(options (world parallel-prolog))
  ((try-each ((?head . ?body) . ?assertions-left) ?goal)
   (parallel-or (sequential-and (= ?head ?goal) (parallel-and . ?body))
                (try-each ?assertions-left ?goal))))

(define-predicate sequential-and :(options (world parallel-prolog))
  ((sequential-and . ?predications) (and . ?predications)))

(define-predicate primitive-predicate :(options (world parallel-prolog))
  ((primitive-predicate cases))
  ((primitive-predicate bag-of))
  ((primitive-predicate set-of))
  ((primitive-predicate lazy-bag-of))
  ((primitive-predicate lazy-set-of))
  ((primitive-predicate eager-bag-of))
  ((primitive-predicate eager-set-of))
  ((primitive-predicate lisp-value))
  ((primitive-predicate lisp-command))
  ((primitive-predicate lisp-predicate))
  ((primitive-predicate call))
  ((primitive-predicate try-each))
  ((primitive-predicate sequential-and))
  ((primitive-predicate parallel-and))
  ((primitive-predicate parallel-or)))

(define-predicate parallel-prove
  ((parallel-prove ?goal) ?goal))

(define-predicate parallel-and 
  ((parallel-and))
  ((parallel-and ?goal-1) (parallel-prove ?goal-1))
  ((parallel-and ?goal-1 ?goal-2)
   (eager-bag-of ?bag-1 ?goal-1 (parallel-prove ?goal-1))
   (eager-bag-of ?bag-2 ?goal-2 (parallel-prove ?goal-2))
   (intertwine ?goal-1 ?bag-1 ?goal-2 ?bag-2))
  ((parallel-and ?goal-1 ?goal-2 ?goal-3 . ?more-goals)
   (parallel-and (parallel-and ?goal-1 ?goal-2)
                 (parallel-and ?goal-3 . ?more-goals))))

(define-predicate intertwine 
  ((intertwine ?goal-1 ?bag-1 ?goal-2 ?bag-2)
   (intertwine ?goal-1 ?bag-1 () ?goal-2 ?bag-2 ()))
  ((intertwine ?goal-1 ?untouched-1 ?touched-1
               ?goal-2 ?untouched-2 ?touched-2)
   (cases ((faster ?untouched-1 ?untouched-2)
           (cases ((= ?untouched-1 (?goal-1-instantiated . ?new-untouched-1))
                   (or (and (= ?goal-1 ?goal-1-instantiated)
                            (member ?goal-2 ?touched-2))
                       (intertwine ?goal-2 ?untouched-2 ?touched-2
                                   ?goal-1 ?new-untouched-1
                                   (?goal-1-instantiated . ?touched-1))))
                  ((member ?goal-1 ?touched-1)
                   (member ?goal-2 ?untouched-2))))
          ((intertwine ?goal-2 ?untouched-2 ?touched-2
                       ?goal-1 ?untouched-1 ?touched-1)))))

(define-predicate parallel-or 
  ((parallel-or ?goal-1) (parallel-prove ?goal-1))
  ((parallel-or ?goal-1 ?goal-2)
   (eager-bag-of ?bag-1 ?goal-1 (parallel-prove ?goal-1))
   (eager-bag-of ?bag-2 ?goal-2 (parallel-prove ?goal-2))
   (cases ((faster ?bag-1 ?bag-2) (alternate ?goal-1 ?bag-1 ?goal-2 ?bag-2))
          ((alternate ?goal-2 ?bag-2 ?goal-1 ?bag-1))))
  ((parallel-or ?goal-1 ?goal-2 ?goal-3 . ?more-goals)
   (parallel-or (parallel-or ?goal-1 ?goal-2)
                (parallel-or ?goal-3 . ?more-goals))))

(define-predicate alternate 
  ((alternate ?goal-1 (?goal-1-instantiated . ?bag-left-1) ?goal-2 ?bag-2)
   (or (= ?goal-1 ?goal-1-instantiated)
       (cases ((faster ?bag-2 ?bag-left-1)
               (alternate ?goal-2 ?bag-2 ?goal-1 ?bag-left-1))
              ((alternate ?goal-1 ?bag-left-1 ?goal-2 ?bag-2)))))
  ((alternate ? () ?goal-2 ?bag-2)
   (member ?goal-2 ?bag-2)))

(define-predicate parallel-call ;;another kind of call
  ((parallel-call ?goal)
   (eager-bag-of ?instantiated-goals ?goal ?goal)
   (member ?goal ?instantiated-goals)))

(define-predicate pipelined-and
  ((pipelined-and))
  ((pipelined-and ?goal . ?more-goals)
   (eager-bag-of ?instantiated-goals ?goal ?goal)
   (member ?goal ?instantiated-goals)
   (pipelined-and . ?more-goals)))


