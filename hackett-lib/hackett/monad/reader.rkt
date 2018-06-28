#lang hackett

(require hackett/monad/trans
         hackett/monad/trans/error
         (rename-in hackett/monad/trans/reader
                    [ask trans:ask]
                    [local trans:local]
                    [asks trans:asks]))

(provide (class Monad-Reader) (rename-out [reader asks])
         (data Reader/T) run-reader/t (for-type Reader) run-reader)

(class (Monad m) => (Monad-Reader r m) #:fundeps [[m -> r]]
  [ask : (m r)]
  [local : (forall [a] {{r -> r} -> (m a) -> (m a)})]
  [reader : (forall [a] {{r -> a} -> (m a)})])

(instance (forall [r] (Monad-Reader r (-> r)))
  [ask id]
  [local (flip .)]
  [reader $])

(instance (forall [r m] (Monad m) => (Monad-Reader r (Reader/T r m)))
  [ask trans:ask]
  [local trans:local]
  [reader trans:asks])

(instance (forall [r e m] (Monad-Reader r m) => (Monad-Reader r (Error/T e m)))
  [ask (lift ask)]
  [local {map-error/t . local}]
  [reader {lift . reader}])
