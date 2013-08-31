;;; -*- Mode: Lisp; Package: Puser; Base: 10. ; Options: ((World Sample-Grammar)); -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;a sample grammar in LM-Prolog using the Grammar Kit

(define-rules sentence
  (--> (sentence (sentence ?noun-phrase ?verb-phrase))
       (noun-phrase ?noun-phrase)
       (verb-phrase ?verb-phrase)))

(define-rules noun-phrase
  (--> (noun-phrase (noun-phrase ?noun))
       (noun ?noun))
  (--> (noun-phrase (noun-phrase ?determiner ?noun))
       (determiner ?determiner)
       (noun ?noun))
  (--> (noun-phrase (noun-phrase ?adjectives ?noun))
       (adjectives ?adjectives)
       (noun ?noun))
  (--> (noun-phrase (noun-phrase ?determiner (adjectives . ?adjectives) ?noun))
       (determiner ?determiner)
       (adjectives ?adjectives)
       (noun ?noun))
;A possible extension.
;  (--> (noun-phrase (noun-phrase that ?sentence))
;       (terminal that)
;       (sentence ?sentence))
  )

(define-rules adjectives
  (--> (adjectives (?adjective))
       (adjective ?adjective))
  (--> (adjectives (?adjective . ?more-adjectives))
       (adjective ?adjective)
       (adjectives ?more-adjectives)))

(define-rules determiner
  (--> (determiner (determiner ?word))
       (is-word ?word determiner)))

(define-rules adjective
  (--> (adjective (adjective ?word))
       (is-word ?word adjective)))

(define-rules noun
  (--> (noun (noun ?word))
       (is-word ?word noun)))

(define-rules verb-phrase
  (--> (verb-phrase (verb-phrase ?verb))
       (verb ?verb))
  (--> (verb-phrase (verb-phrase ?verb ?noun-phrase))
       (verb ?verb)
       (noun-phrase ?noun-phrase)))

(define-rules verb
  (--> (verb (verb ?word))
       (is-word ?word verb)))

(comment ;;one way to eliminate duplicate ajectives
(DEFINE-RULES ADJECTIVES
              (-->
               (ADJECTIVES (?ADJECTIVE) ?ADJECTIVES-SEEN)
               (ADJECTIVE ?ADJECTIVE)
               (CALL (CANNOT-PROVE (MEMBER ?ADJECTIVE ?ADJECTIVES-SEEN))))
              (-->
               (ADJECTIVES (?ADJECTIVE . ?MORE-ADJECTIVES) ?ADJECTIVES-SEEN)
               (ADJECTIVE ?ADJECTIVE)
               (CALL (CANNOT-PROVE (MEMBER ?ADJECTIVE ?ADJECTIVES-SEEN)))
               (ADJECTIVES ?MORE-ADJECTIVES (?ADJECTIVE . ?ADJECTIVES-SEEN))))
)
