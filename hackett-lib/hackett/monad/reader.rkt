#lang hackett

(require hackett/data/identity
         hackett/monad/trans)

(provide (data ReaderT) run-reader-t run-reader ask asks local)

(data (ReaderT r m a) (ReaderT {r -> (m a)}))

(defn run-reader-t : (forall [r m a] {(ReaderT r m a) -> r -> (m a)})
  [[(ReaderT f)] f])

(defn run-reader : (forall [r a] {(ReaderT r Identity a) -> r -> a})
  [[x r] (run-identity (run-reader-t x r))])

(instance (forall [r] (MonadTrans (ReaderT r)))
  [lift {ReaderT . const}])

(instance (forall [r m] (Functor m) => (Functor (ReaderT r m)))
  [map (λ [f (ReaderT x)] (ReaderT (λ [r] (map f (x r)))))])

(instance (forall [r m] (Applicative m) => (Applicative (ReaderT r m)))
  [pure {ReaderT . const . pure}]
  [<*> (λ [(ReaderT f) (ReaderT x)] (ReaderT (λ [r] {(f r) <*> (x r)})))])

(instance (forall [r m] (Monad m) => (Monad (ReaderT r m)))
  [join (λ [(ReaderT x)]
          (ReaderT (λ [r] (do [x* <- (x r)]
                               (case x* [(ReaderT y) (y r)])))))])

(def ask : (forall [r m] (Applicative m) => (ReaderT r m r))
  (ReaderT (λ [r] (pure r))))

(defn asks : (forall [r m a] (Applicative m) => {{r -> a} -> (ReaderT r m a)})
  [[f] (ReaderT (λ [r] (pure (f r))))])

(defn local : (forall [r m a] {{r -> r} -> (ReaderT r m a) -> (ReaderT r m a)})
  [[f x] (ReaderT (λ [r] (run-reader-t x (f r))))])
