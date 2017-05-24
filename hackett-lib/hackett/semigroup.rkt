#lang hackett/private/kernel

(require (except-in hackett/private/class class)
         (only-in hackett/private/prim append/String)
         hackett/private/provide)

(provide (class Semigroup))

(class (Semigroup a)
  [++ : {a -> a -> a}
      #:fixity right])

(instance (Semigroup String)
  [++ append/String])
