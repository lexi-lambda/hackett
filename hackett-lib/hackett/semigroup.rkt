#lang hackett/private/kernel

(require (except-in hackett/private/adt data)
         (except-in hackett/private/class class)
         (only-in hackett/private/prim append/String)
         hackett/data/list
         hackett/private/provide)

(provide (class Semigroup))

(class (Semigroup a)
  [++ : {a -> a -> a}
      #:fixity right])

(instance (Semigroup String)
  [++ append/String])

(instance (∀ [a] (Semigroup (List a)))
  [++ (λ* [[{z :: zs} ys] {z :: {zs ++ ys}}]
          [[nil       ys] ys])])
