#lang s-exp "lang-unify.rkt"

(data Maybe-Integer
      (just Integer)
      nothing)

(data Either-String-Maybe-Integer
      (left String)
      (right Maybe-Integer))

(case (right nothing)
  [(left str) 0]
  [(right (just x)) x]
  [(right nothing) 0])
