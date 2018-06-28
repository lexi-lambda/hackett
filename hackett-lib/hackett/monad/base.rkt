#lang hackett/base

(require hackett/private/prim/base
         hackett/private/prim/type)

(provide (class Monad-Base))

(class (Monad m) => (Monad-Base b m) #:fundeps [[m -> b]]
  [lift/base : (forall [a] {(b a) -> (m a)})])

(instance (Monad-Base IO IO)
  [lift/base id])
