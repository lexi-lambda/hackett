#lang hackett

(provide (data Identity) get-identity)

(data (Identity a) (identity a))

(defn get-identity : (forall [a] {(Identity a) -> a})
  [[(identity x)] x])

(instance (forall [a] (Show a) => (Show (Identity a)))
  [show (λ [(identity x)] {"(identity " ++ (show x) ++ ")"})])

(instance (forall [a] (Eq a) => (Eq (Identity a)))
  [== (λ [(identity x) (identity y)] {x == y})])

(instance (forall [a] (Semigroup a) => (Semigroup (Identity a)))
  [++ (λ [(identity x) (identity y)] (identity {x ++ y}))])

(instance (forall [a] (Monoid a) => (Monoid (Identity a)))
  [mempty (identity mempty)])

(instance (Functor Identity)
  [map (λ [f (identity x)] (identity (f x)))])

(instance (Applicative Identity)
  [pure identity]
  [<*> (λ [(identity f) (identity x)] (identity (f x)))])

(instance (Monad Identity)
  [join (λ [(identity (identity x))] (identity x))])
