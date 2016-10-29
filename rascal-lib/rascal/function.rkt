#lang rascal/private/kernel

(provide id const flip)

(def id : (forall [a] (-> a a))
  (λ (x) x))

(def const : (forall [a b] (-> a (-> b a)))
  (λ (y x) y))

(def flip : (forall [a b c] (-> (-> a (-> b c))
                                (-> b (-> a c))))
  (λ (f x y) (f y x)))
