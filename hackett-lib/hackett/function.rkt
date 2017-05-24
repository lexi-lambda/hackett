#lang hackett/private/kernel

(provide id compose const flip)

(def id : (∀ [a] {a -> a})
  (λ [x] x))

(def compose : (∀ [a b c] {{b -> c} -> {a -> b} -> a -> c})
  (λ [f g x] (f (g x))))

(def const : (∀ [a b] {a -> b -> a})
  (λ [x y] x))

(def flip : (∀ [a b c] {{a -> b -> c} -> b -> a -> c})
  (λ [f x y] (f y x)))
