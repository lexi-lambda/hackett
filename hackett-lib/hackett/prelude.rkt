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
         (all-from-out hackett/private/prim)

         (data List) sequence traverse)

;; ---------------------------------------------------------------------------------------------------
;; List

(data (List a) (cons a (List a)) nil)

(instance (Functor List)
  [map (λ [f x] (case x [(cons y ys) (cons (f y) (map f ys))]
                        [nil nil]))])

(instance (Applicative List)
  [pure (λ [x] (cons x nil))]
  [apply (λ [f] (ap f))])

(instance (Monad List)
  [join (λ [xss] (case xss
                   [nil nil]
                   [(cons ys yss) (case ys
                                    [nil (join yss)]
                                    [(cons z zs) (cons z (join (cons zs yss)))])]))])

(def sequence : (∀ [f a] (=> [(Functor f) (Applicative f)] (-> (List (f a)) (f (List a)))))
  (λ [xs] (case xs [nil (pure nil)]
                   [(cons y ys) (apply (map cons y) (sequence ys))])))

(def traverse : (∀ [f a b] (=> [(Functor f) (Applicative f)]
                               (-> (-> a (f b)) (-> (List a) (f (List b))))))
  (λ [f xs] (sequence (map f xs))))
