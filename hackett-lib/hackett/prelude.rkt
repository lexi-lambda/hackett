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
  [show (λ [x] (case x [unit "unit"]))])

(instance (Show Bool)
  [show (λ [x] (case x [true "true"]
                       [false "false"]))])

(instance (Show Integer)
  [show show/Integer])

(instance (Show String)
  [show (λ [str] {"\"" ++ str ++ "\""})])

(instance ∀ [a] (Show a) => (Show (Maybe a))
  [show (λ [x] (case x [nothing "nothing"]
                       [(just x) {"(just " ++ (show x) ++ ")"}]))])

(instance ∀ [a b] (Show a) (Show b) => (Show (Tuple a b))
  [show (λ [x] (case x [(tuple a b) {"(tuple " ++ (show a) ++ " " ++ (show b) ++ ")"}]))])

;; ---------------------------------------------------------------------------------------------------
;; Eq

(class (Eq a)
  [== : {a -> a -> Bool}])

(instance (Eq Unit)
  [== (λ [x y] (case x [unit (case y [unit true])]))])

(instance (Eq Bool)
  [== (λ [x y] (case x [true y]
                       [false (not y)]))])

(instance (Eq Integer)
  [== equal?/Integer])

(instance (Eq String)
  [== equal?/String])

(instance ∀ [a] (Eq a) => (Eq (Maybe a))
  [== (λ [x y] (case x [(just a)
                        (case y [(just b) (== a b)]
                                [nothing false])]
                       [nothing
                        (case y [(just _) false]
                                [nothing true])]))])

(instance ∀ [a b] (Eq a) (Eq b) => (Eq (Tuple a b))
  [== (λ [x y] (case x [(tuple a b) (case y [(tuple c d) (and (== a c) (== b d))])]))])

;; ---------------------------------------------------------------------------------------------------
;; List

(data (List a)
  {a :: (List a)} #:fixity right
  nil)

(instance ∀ [a] (Show a) => (Show (List a))
  [show (λ [xs] (case xs [nil "nil"]
                         [{y :: ys} {"{" ++ (show y) ++ " :: " ++ (show ys) ++ "}"}]))])

(instance ∀ [a] (Semigroup (List a))
  [++ (λ [xs ys] (case xs
                   [nil ys]
                   [{z :: zs}
                    {z :: {zs ++ ys}}]))])

(instance ∀ [a] (Monoid (List a))
  [mempty nil])

(instance (Functor List)
  [map (λ [f x] (case x [{y :: ys} {(f y) :: (map f ys)}]
                        [nil nil]))])

(instance (Applicative List)
  [pure (λ [x] {x :: nil})]
  [<*> ap])

(instance (Monad List)
  [join (λ [xss] (case xss
                   [nil nil]
                   [{ys :: yss} (case ys
                                  [nil (join yss)]
                                  [{z :: zs} {z :: (join {zs :: yss})}])]))])

(def sequence : (∀ [f a] (Applicative f) => {(List (f a)) -> (f (List a))})
  (λ [xs] (case xs [nil (pure nil)]
                   [{y :: ys} {:: <$> y <*> (sequence ys)}])))

(def traverse : (∀ [f a b] (Applicative f) => {{a -> (f b)} -> (List a) -> (f (List b))})
  (λ [f xs] (sequence (map f xs))))
