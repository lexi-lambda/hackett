#lang hackett/private/kernel

(require (only-in racket/base all-from-out except-in)
         hackett/applicative
         hackett/data/bool
         hackett/data/maybe
         hackett/data/tuple
         hackett/data/unit
         hackett/function
         hackett/functor
         hackett/monad
         hackett/monoid
         hackett/semigroup
         (except-in hackett/private/adt data)
         (except-in hackett/private/class class)
         hackett/private/prim
         hackett/private/provide)

(provide (all-from-out hackett/applicative)
         (all-from-out hackett/data/bool)
         (all-from-out hackett/data/maybe)
         (all-from-out hackett/data/tuple)
         (all-from-out hackett/data/unit)
         (all-from-out hackett/function)
         (all-from-out hackett/functor)
         (all-from-out hackett/monad)
         (all-from-out hackett/monoid)
         (all-from-out hackett/semigroup)

         IO main print error! undefined!
         + - * quotient! remainder! < > <= >=

         (class Show)
         (class Eq)

         (data List) sequence traverse)

;; ---------------------------------------------------------------------------------------------------

(def undefined! : (∀ [a] a)
  (error! "undefined!"))

;; ---------------------------------------------------------------------------------------------------
;; Show

(class (Show a)
  [show : {a -> String}])

(instance (Show Unit)
  [show (λ [unit] "unit")])

(instance (Show Bool)
  [show (λ* [[true ] "true"]
            [[false] "false"])])

(instance (Show Integer)
  [show show/Integer])

(instance (Show String)
  [show (λ [str] {"\"" ++ str ++ "\""})])

(instance ∀ [a] (Show a) => (Show (Maybe a))
  [show (λ* [[(just x)] {"(just " ++ (show x) ++ ")"}]
            [[nothing ] "nothing"])])

(instance ∀ [a b] (Show a) (Show b) => (Show (Tuple a b))
  [show (λ [(tuple a b)] {"(tuple " ++ (show a) ++ " " ++ (show b) ++ ")"})])

;; ---------------------------------------------------------------------------------------------------
;; Eq

(class (Eq a)
  [== : {a -> a -> Bool}])

(instance (Eq Unit)
  [== (λ [unit unit] true)])

(instance (Eq Bool)
  [== (λ* [[true  y] y]
          [[false y] (not y)])])

(instance (Eq Integer)
  [== equal?/Integer])

(instance (Eq String)
  [== equal?/String])

(instance ∀ [a] (Eq a) => (Eq (Maybe a))
  [== (λ* [[(just a) (just b)] (== a b)]
          [[nothing  nothing ] true]
          [[_        _       ] false])])

(instance ∀ [a b] (Eq a) (Eq b) => (Eq (Tuple a b))
  [== (λ [(tuple a b) (tuple c d)] (and (== a c) (== b d)))])

;; ---------------------------------------------------------------------------------------------------
;; List

(data (List a)
  {a :: (List a)} #:fixity right
  nil)

(instance ∀ [a] (Show a) => (Show (List a))
  [show (λ* [[{y :: ys}] {"{" ++ (show y) ++ " :: " ++ (show ys) ++ "}"}]
            [[nil      ] "nil"])])

(instance ∀ [a] (Semigroup (List a))
  [++ (λ* [[{z :: zs} ys] {z :: {zs ++ ys}}]
          [[nil       ys] ys])])

(instance ∀ [a] (Monoid (List a))
  [mempty nil])

(instance (Functor List)
  [map (λ* [[f {y :: ys}] {(f y) :: (map f ys)}]
           [[_ nil      ] nil])])

(instance (Applicative List)
  [pure (λ [x] {x :: nil})]
  [<*> ap])

(instance (Monad List)
  [join (λ* [[{{z :: zs} :: yss}] {z :: (join {zs :: yss})}]
            [[{nil       :: yss}] (join yss)]
            [[nil               ] nil])])

(defn sequence : (∀ [f a] (Applicative f) => {(List (f a)) -> (f (List a))})
  [[{y :: ys}] {:: <$> y <*> (sequence ys)}]
  [[nil      ] (pure nil)])

(defn traverse : (∀ [f a b] (Applicative f) => {{a -> (f b)} -> (List a) -> (f (List b))})
  [[f xs] (sequence (map f xs))])
