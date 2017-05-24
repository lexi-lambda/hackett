#lang hackett/private/kernel

(require hackett/private/provide)

(provide (class Applicative))

(class (Applicative f)
  [pure : (∀ [a] {a -> (f a)})]
  [<*> : (∀ [a b] {(f {a -> b}) -> (f a) -> (f b)})])
