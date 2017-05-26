#lang hackett/private/kernel

(require (except-in hackett/private/class class)
         hackett/private/provide
         hackett/semigroup)

(provide (class Monoid))

(class (Semigroup a) => (Monoid a)
  [mempty : a])

(instance (Monoid String)
  [mempty ""])
