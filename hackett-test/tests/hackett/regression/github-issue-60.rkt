#lang hackett

(class (Base a)
  [base : {a -> a -> a -> a}])

(class (Middle a)
  [middle : {a -> a -> a}])

(class (Top a)
  [top : {a -> a}])

(instance (forall [a] (Middle a) => (Base a))
  [base (λ [_] middle)])

(instance (forall [a] (Top a) => (Middle a))
  [middle (λ [_] top)])
