#lang hackett/private/kernel

(require (only-in racket/base except-in)
         hackett/applicative
         hackett/function
         hackett/functor
         hackett/monad
         (except-in hackett/private/adt data)
         (except-in hackett/private/class class)
         hackett/private/provide)

(provide (data Maybe) maybe from-maybe)

(data (Maybe a) (just a) nothing)

(def maybe : (∀ [a b] (-> b (-> (-> a b) (-> (Maybe a) b))))
  (λ [v f m] (case m [(just x) (f x)]
                     [nothing v])))

(def from-maybe : (∀ [a b] (-> a (-> (Maybe a) a)))
  (λ [v] (maybe v id)))

(instance (Functor Maybe)
  [map (λ [f m] (case m [(just x) (just (f x))]
                        [nothing nothing]))])

(instance (Applicative Maybe)
  [pure just]
  [apply (λ [f] (ap f))])

(instance (Monad Maybe)
  [join (λ [x] (case x [(just (just x)) (just x)]
                       [_ nothing]))])
