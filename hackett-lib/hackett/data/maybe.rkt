#lang hackett/base

(require hackett/private/prim)

(provide (data Maybe) maybe from-maybe)

(defn maybe : (∀ [a b] {b -> {a -> b} -> (Maybe a) -> b})
  [[_ f (Just x)] (f x)]
  [[v _ Nothing ] v])

(defn from-maybe : (∀ [a b] {a -> (Maybe a) -> a})
  [[v] (maybe v id)])
