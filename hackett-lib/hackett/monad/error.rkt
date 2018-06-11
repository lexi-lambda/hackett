#lang hackett

(require hackett/monad/trans
         (rename-in hackett/monad/trans/error
                    [throw trans:throw]
                    [catch trans:catch])
         hackett/monad/trans/reader)

(provide (class Monad-Error)
         (data Error/T) run-error/t (for-type Error) run-error)

(class (Monad m) => (Monad-Error e m) #:fundeps [[m -> e]]
  [throw : (forall [a] {e -> (m a)})]
  [catch : (forall [a] {(m a) -> {e -> (m a)} -> (m a)})])

(instance (forall [e] (Monad-Error e (Either e)))
  [throw Left]
  [catch (λ* [[(Right x) _] (Right x)]
             [[(Left x) f] (f x)])])

(instance (forall [e m] (Monad m) => (Monad-Error e (Error/T e m)))
  [throw trans:throw]
  [catch trans:catch])

(instance (forall [e r m] (Monad-Error e m) => (Monad-Error e (Reader/T r m)))
  [throw {lift . throw}]
  [catch (lift-catch/reader/t catch)])
