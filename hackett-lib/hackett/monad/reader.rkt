#lang hackett

(require hackett/data/identity
         hackett/monad/trans)

(provide (data ReaderT) run-reader-t run-reader ask asks local)

(data (ReaderT r m a) (reader-t {r -> (m a)}))

(defn run-reader-t : (forall [r m a] {(ReaderT r m a) -> r -> (m a)})
  [[(reader-t f)] f])

(defn run-reader : (forall [r a] {(ReaderT r Identity a) -> r -> a})
  [[x r] (run-identity (run-reader-t x r))])

(instance (forall [r] (MonadTrans (ReaderT r)))
  [lift {reader-t . const}])

(instance (forall [r m] (Functor m) => (Functor (ReaderT r m)))
  [map (λ [f (reader-t x)] (reader-t (λ [r] (map f (x r)))))])

(instance (forall [r m] (Applicative m) => (Applicative (ReaderT r m)))
  [pure {reader-t . const . pure}]
  [<*> (λ [(reader-t f) (reader-t x)] (reader-t (λ [r] {(f r) <*> (x r)})))])

(instance (forall [r m] (Monad m) => (Monad (ReaderT r m)))
  [join (λ [(reader-t x)]
          (reader-t (λ [r] (do [x* <- (x r)]
                               (case x* [(reader-t y) (y r)])))))])

(def ask : (forall [r m] (Applicative m) => (ReaderT r m r))
  (reader-t (λ [r] (pure r))))

(defn asks : (forall [r m a] (Applicative m) => {{r -> a} -> (ReaderT r m a)})
  [[f] (reader-t (λ [r] (pure (f r))))])

(defn local : (forall [r m a] {{r -> r} -> (ReaderT r m a) -> (ReaderT r m a)})
  [[f x] (reader-t (λ [r] (run-reader-t x (f r))))])
