#lang hackett/private/kernel

(require hackett/data/unit
         hackett/function
         hackett/private/provide)

(provide (class Functor) ignore
         (rename-out [map <$>]))

(class (Functor f)
  [map : (∀ [a b] {{a -> b} -> (f a) -> (f b)})])

(def ignore : (∀ [f a] (Functor f) => {(f a) -> (f Unit)})
  (map (const unit)))
