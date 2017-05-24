#lang hackett/private/kernel

(require (except-in hackett/private/class class)
         hackett/private/provide)

(provide (class Monoid))

(class (Monoid a)
  [mempty : a])

(instance (Monoid String)
  [mempty ""])
