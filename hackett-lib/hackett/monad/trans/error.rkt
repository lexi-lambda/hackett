#lang hackett

(require hackett/data/identity
         hackett/monad/base
         hackett/monad/trans)

(provide (data Error/T) run-error/t map-error/t (for-type Error) run-error throw catch)

(data (Error/T e m a) (Error/T (m (Either e a))))

(defn run-error/t : (forall [e m a] {(Error/T e m a) -> (m (Either e a))})
  [[(Error/T x)] x])

(defn map-error/t : (forall [e e* a b m n] {{(m (Either e a)) -> (n (Either e* b))}
                                            -> (Error/T e m a) -> (Error/T e* n b)})
  [[f m] (Error/T (f (run-error/t m)))])

(type (Error e) (Error/T e Identity))

(defn run-error : (forall [e a] {((Error e) a) -> (Either e a)})
  [[x] (run-identity (run-error/t x))])

(instance (forall [e m] (Functor m) => (Functor (Error/T e m)))
  [map (λ [f (Error/T x)] (Error/T (map (map f) x)))])

(instance (forall [e m] (Monad m) => (Applicative (Error/T e m)))
  [pure {Error/T . pure . Right}]
  [<*> (λ [(Error/T f) (Error/T x)]
         (Error/T (do [f* <- f]
                      (case f*
                        [(Right f**)
                         {(λ [x*] {f** <$> x*}) <$> x}]
                        [(Left e)
                         (pure (Left e))]))))])

(instance (forall [e m] (Monad m) => (Monad (Error/T e m)))
  [join (λ [(Error/T x)]
          (Error/T (do [x* <- x]
                       (case x*
                         [(Right (Error/T x**)) x**]
                         [(Left e) (pure (Left e))]))))])

(instance (forall [e] (Monad-Trans (Error/T e)))
  [lift {Error/T . (map Right)}])

(instance (forall [b e m] (Monad-Base b m) => (Monad-Base b (Error/T e m)))
  [lift/base {lift . lift/base}])

(def throw : (forall [e a m] (Applicative m) => {e -> (Error/T e m a)})
  {Error/T . pure . Left})

(defn catch : (forall [e e* a m] (Monad m) =>
                      {(Error/T e m a) -> {e -> (Error/T e* m a)} -> (Error/T e* m a)})
  [[(Error/T x) f]
   (Error/T (do [x* <- x]
                (case x*
                  [(Right x**) (pure (Right x**))]
                  [(Left e) (case (f e)
                              [(Error/T y) y])])))])
