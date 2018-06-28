#lang hackett

(provide (class Monad-Trans))

(class (Monad-Trans t)
  [lift : (forall [m a] (Monad m) => {(m a) -> (t m a)})])
