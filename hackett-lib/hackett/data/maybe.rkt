#lang hackett/private/kernel

(require (only-in racket/base except-in)
         hackett/function
         (except-in hackett/private/adt data)
         hackett/private/provide)

(provide (data Maybe) maybe from-maybe map/maybe join/maybe and-then/maybe)

(data (Maybe a) (just a) nothing)

(def maybe : (∀ [a b] (-> b (-> (-> a b) (-> (Maybe a) b))))
  (λ [v f m] (case m [(just x) (f x)]
                     [nothing v])))

(def from-maybe : (∀ [a b] (-> a (-> (Maybe a) a)))
  (λ [v] (maybe v id)))

(def map/maybe : (∀ [a b] (-> (-> a b) (-> (Maybe a) (Maybe b))))
  (λ [f m] (case m [(just x) (just (f x))]
                   [nothing nothing])))

(def join/maybe : (∀ [a] (-> (Maybe (Maybe a)) (Maybe a)))
  (λ [x] (case x [(just (just x)) (just x)]
                 [_ nothing])))

(def and-then/maybe : (∀ [a b] (-> (Maybe a) (-> (-> a (Maybe b)) (Maybe b))))
  (λ [m f] (join/maybe (map/maybe f m))))
