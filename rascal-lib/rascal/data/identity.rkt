#lang rascal/base

(require rascal/monad)

(provide (data Identity))

(data (Identity a)
  (identity a))

(def run-identity : (forall [a] {(Identity a) . -> . a})
  (λ (x) (case x [(identity v) v])))

(instance (Functor Identity)
  [map (λ (f x) (identity (f (run-identity x))))])

(instance (Applicative Identity)
  [pure identity]
  [<*> (λ (f x) (identity ((run-identity f) (run-identity x))))])

(instance (Monad Identity)
  [join (λ (x) (run-identity x))])
