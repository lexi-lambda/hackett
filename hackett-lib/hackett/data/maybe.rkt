#lang hackett/private/kernel

(require hackett/applicative
         hackett/function
         hackett/functor
         hackett/monad
         (except-in hackett/private/adt data)
         (except-in hackett/private/class class)
         hackett/private/provide)

(provide (data Maybe) maybe from-maybe)

(data (Maybe a) (just a) nothing)

(defn maybe : (∀ [a b] {b -> {a -> b} -> (Maybe a) -> b})
  [[_ f (just x)] (f x)]
  [[v _ nothing ] v])

(defn from-maybe : (∀ [a b] {a -> (Maybe a) -> a})
  [[v] (maybe v id)])

(instance (Functor Maybe)
  [map (λ* [[f (just x)] (just (f x))]
           [[_ nothing ] nothing])])

(instance (Applicative Maybe)
  [pure just]
  [<*> ap])

(instance (Monad Maybe)
  [join (λ* [[(just (just x))] (just x)]
            [[_              ] nothing])])
