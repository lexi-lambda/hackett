#lang hackett

(require hackett/data/identity
         hackett/monad/trans)

(provide (data ErrorT) run-error-t run-error throw catch)

(data (ErrorT e m a) (error-t (m (Either e a))))

(defn run-error-t : (forall [e m a] {(ErrorT e m a) -> (m (Either e a))})
  [[(error-t x)] x])

(defn run-error : (forall [e a] {(ErrorT e Identity a) -> (Either e a)})
  [[x] (run-identity (run-error-t x))])

(instance (forall [e] (MonadTrans (ErrorT e)))
  [lift {error-t . (map right)}])

(instance (forall [e m] (Functor m) => (Functor (ErrorT e m)))
  [map (λ [f (error-t x)] (error-t (map (map f) x)))])

(instance (forall [e m] (Monad m) => (Applicative (ErrorT e m)))
  [pure {error-t . pure . right}]
  [<*> (λ [(error-t f) (error-t x)]
         (error-t (do [f* <- f]
                      (case f*
                        [(right f**)
                         {(λ [x*] {f** <$> x*}) <$> x}]
                        [(left e)
                         (pure (left e))]))))])

(instance (forall [e m] (Monad m) => (Monad (ErrorT e m)))
  [join (λ [(error-t x)]
          (error-t (do [x* <- x]
                       (case x*
                         [(right (error-t x**)) x**]
                         [(left e) (pure (left e))]))))])

(def throw : (forall [e a m] (Applicative m) => {e -> (ErrorT e m a)})
  {error-t . pure . left})

(defn catch : (forall [e e* a m] (Monad m) =>
                      {(ErrorT e m a) -> {e -> (ErrorT e* m a)} -> (ErrorT e* m a)})
  [[(error-t x) f]
   (error-t (do [x* <- x]
                (case x*
                  [(right x**) (pure (right x**))]
                  [(left e) (case (f e)
                              [(error-t y) y])])))])
