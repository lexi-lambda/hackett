#lang hackett

(provide (class MonadTrans))

(class (MonadTrans t)
  [lift : (forall [m a] (Monad m) => {(m a) -> (t m a)})])
