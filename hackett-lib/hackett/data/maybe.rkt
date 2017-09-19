#lang hackett/base

(require hackett/private/prim)

(provide maybe from-maybe)

(defn maybe : (∀ [a b] {b -> {a -> b} -> (Maybe a) -> b})
  [[_ f (just x)] (f x)]
  [[v _ nothing ] v])

(defn from-maybe : (∀ [a b] {a -> (Maybe a) -> a})
  [[v] (maybe v id)])
