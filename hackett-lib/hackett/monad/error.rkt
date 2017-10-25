#lang hackett

(require hackett/data/identity
         hackett/monad/trans)

(provide (data ErrorT) run-error-t run-error throw catch)

(data (ErrorT e m a) (ErrorT (m (Either e a))))

(defn run-error-t : (forall [e m a] {(ErrorT e m a) -> (m (Either e a))})
  [[(ErrorT x)] x])

(defn run-error : (forall [e a] {(ErrorT e Identity a) -> (Either e a)})
  [[x] (run-identity (run-error-t x))])

(instance (forall [e] (MonadTrans (ErrorT e)))
  [lift {ErrorT . (map Right)}])

(instance (forall [e m] (Functor m) => (Functor (ErrorT e m)))
  [map (λ [f (ErrorT x)] (ErrorT (map (map f) x)))])

(instance (forall [e m] (Monad m) => (Applicative (ErrorT e m)))
  [pure {ErrorT . pure . Right}]
  [<*> (λ [(ErrorT f) (ErrorT x)]
         (ErrorT (do [f* <- f]
                     (case f*
                       [(Right f**)
                        {(λ [x*] {f** <$> x*}) <$> x}]
                       [(Left e)
                        (pure (Left e))]))))])

(instance (forall [e m] (Monad m) => (Monad (ErrorT e m)))
  [join (λ [(ErrorT x)]
          (ErrorT (do [x* <- x]
                      (case x*
                        [(Right (ErrorT x**)) x**]
                        [(Left e) (pure (Left e))]))))])

(def throw : (forall [e a m] (Applicative m) => {e -> (ErrorT e m a)})
  {ErrorT . pure . Left})

(defn catch : (forall [e e* a m] (Monad m) =>
                      {(ErrorT e m a) -> {e -> (ErrorT e* m a)} -> (ErrorT e* m a)})
  [[(ErrorT x) f]
   (ErrorT (do [x* <- x]
               (case x*
                 [(Right x**) (pure (Right x**))]
                 [(Left e) (case (f e)
                             [(ErrorT y) y])])))])
