#lang hackett

(data Nop
  (nop (∀ [a] {a -> a})))
(defn ->nop : (∀ [a] {a -> Nop -> a})
  [[x (nop f)] (f x)])
