#lang hackett/private/kernel

(require hackett/private/adt)

(provide id compose const flip)

(defn id : (∀ [a] {a -> a})
  [[x] x])

(defn compose : (∀ [a b c] {{b -> c} -> {a -> b} -> a -> c})
  [[f g x] (f (g x))])

(defn const : (∀ [a b] {a -> b -> a})
  [[x _] x])

(defn flip : (∀ [a b c] {{a -> b -> c} -> b -> a -> c})
  [[f x y] (f y x)])
