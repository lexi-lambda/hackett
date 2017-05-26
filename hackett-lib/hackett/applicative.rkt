#lang hackett/private/kernel

(require hackett/functor
         hackett/private/provide)

(provide (class Applicative))

(class [(Functor f)] => (Applicative f)
  [pure : (∀ [a] {a -> (f a)})]
  [<*> : (∀ [a b] {(f {a -> b}) -> (f a) -> (f b)})])
