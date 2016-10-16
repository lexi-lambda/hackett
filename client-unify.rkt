#lang s-exp "lang-unify.rkt"

(data Maybe-Integer
      (just Integer)
      nothing)

(let ([just-or-zero (λ x (case x
                           [(just v) v]
                           [nothing 0]))])
  (just-or-zero (just 12)))
