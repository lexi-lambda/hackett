#lang hackett/private/kernel

(require (except-in hackett/private/adt data)
         (except-in hackett/private/class class)
         hackett/functor
         hackett/applicative
         hackett/monad
         hackett/private/provide)

(provide (data List) sequence traverse)

(data (List a)
  {a :: (List a)} #:fixity right
  nil)

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
