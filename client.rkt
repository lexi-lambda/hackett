#lang s-exp "lang.rkt"

(data OneOrTwo
      (One Integer)
      (Two Integer Integer))

(def first
  (λ [x : OneOrTwo]
    (case x
      [(One a) a]
      [(Two a b) a])))

(def last
  (λ [x : OneOrTwo]
    (case x
      [(One a) a]
      [(Two a b) b])))

(first (One 1))
(last (One 1))

(first (Two 1 2))
(last (Two 1 2))
