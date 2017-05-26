#lang hackett/private/kernel

(require (only-in racket/base except-in)
         (except-in hackett/private/adt data)
         hackett/private/provide)

(provide (data Tuple) tuple-cata fst snd)

(data (Tuple a b) (tuple a b))

(defn tuple-cata : (∀ [a b c] {{a -> b -> c} -> (Tuple a b) -> c})
  [[f (tuple x y)] (f x y)])

(defn fst : (∀ [a b] {(Tuple a b) -> a})
  [[(tuple x _)] x])

(defn snd : (∀ [a b] {(Tuple a b) -> b})
  [[(tuple _ x)] x])
