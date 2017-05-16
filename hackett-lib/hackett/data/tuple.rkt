#lang hackett/private/kernel

(require (only-in racket/base except-in)
         (except-in hackett/private/adt data)
         hackett/private/provide)

(provide (data Tuple) tuple-cata fst snd)

(data (Tuple a b) (tuple a b))

(def tuple-cata : (∀ [a b c] (-> (-> a (-> b c)) (-> (Tuple a b) c)))
  (λ [f t] (case t [(tuple x y) (f x y)])))

(def fst : (∀ [a b] (-> (Tuple a b) a))
  (λ [t] (case t [(tuple x _) x])))

(def snd : (∀ [a b] (-> (Tuple a b) b))
  (λ [t] (case t [(tuple _ x) x])))
