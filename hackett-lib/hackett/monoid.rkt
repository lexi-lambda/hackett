#lang hackett/private/kernel

(require (except-in hackett/private/adt data)
         (except-in hackett/private/class class)
         hackett/data/list
         hackett/private/provide
         hackett/semigroup)

(provide (class Monoid))

(class (Semigroup a) => (Monoid a)
  [mempty : a])

(instance (Monoid String)
  [mempty ""])

(instance (∀ [a] (Monoid (List a)))
  [mempty nil])
