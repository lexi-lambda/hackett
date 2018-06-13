#lang hackett

(require hackett/data/identity
         hackett/monad/base
         hackett/monad/trans
         hackett/monad/trans/signatures)

(provide (data Reader/T) run-reader/t lift-catch/reader/t (for-type Reader) run-reader ask asks local)

(data (Reader/T r m a) (Reader/T {r -> (m a)}))

(defn run-reader/t : (forall [r m a] {(Reader/T r m a) -> r -> (m a)})
  [[(Reader/T f)] f])

(defn lift-catch/reader/t : (forall [e r m a] {(Catch e m a) -> (Catch e (Reader/T r m) a)})
  [[f m h] (Reader/T (λ [r] (f (run-reader/t m r) (λ [e] (run-reader/t (h e) r)))))])

(type (Reader r) (Reader/T r Identity))

(defn run-reader : (forall [r a] {((Reader r) a) -> r -> a})
  [[x r] (run-identity (run-reader/t x r))])

(instance (forall [r m] (Functor m) => (Functor (Reader/T r m)))
  [map (λ [f (Reader/T x)] (Reader/T (λ [r] (map f (x r)))))])

(instance (forall [r m] (Applicative m) => (Applicative (Reader/T r m)))
  [pure {Reader/T . const . pure}]
  [<*> (λ [(Reader/T f) (Reader/T x)] (Reader/T (λ [r] {(f r) <*> (x r)})))])

(instance (forall [r m] (Monad m) => (Monad (Reader/T r m)))
  [join (λ [(Reader/T x)]
          (Reader/T (λ [r] (do [x* <- (x r)]
                               (case x* [(Reader/T y) (y r)])))))])

(instance (forall [r] (Monad-Trans (Reader/T r)))
  [lift {Reader/T . const}])

(instance (forall [b r m] (Monad-Base b m) => (Monad-Base b (Reader/T r m)))
  [lift/base {lift . lift/base}])

(def ask : (forall [r m] (Applicative m) => (Reader/T r m r))
  (Reader/T (λ [r] (pure r))))

(defn asks : (forall [r m a] (Applicative m) => {{r -> a} -> (Reader/T r m a)})
  [[f] (Reader/T (λ [r] (pure (f r))))])

(defn local : (forall [r m a] {{r -> r} -> (Reader/T r m a) -> (Reader/T r m a)})
  [[f x] (Reader/T (λ [r] (run-reader/t x (f r))))])