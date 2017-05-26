#lang hackett/private/kernel

(require (only-in racket/base define-syntax for-syntax)
         (for-syntax racket/base
                     syntax/parse/class/paren-shape)
         hackett/applicative
         hackett/function
         hackett/functor
         (only-in hackett/private/adt defn)
         hackett/private/provide
         syntax/parse/define)

(provide (class Monad) =<< >>= do ap)

(class (Applicative m) => (Monad m)
  [join : (∀ [a] {(m (m a)) -> (m a)})])

(defn =<< : (∀ [m a b] (Monad m) => {{a -> (m b)} -> (m a) -> (m b)})
  [[f x] (join (map f x))])

(def >>= : (∀ [m a b] (Monad m) => {(m a) -> {a -> (m b)} -> (m b)})
  (flip =<<))

(define-syntax-parser do
  #:datum-literals [<-]
  [(_ {~and clause [~brackets ~! x:id <- e:expr]} rest ...+)
   (syntax/loc #'clause
     (>>= e (λ [x] (do rest ...))))]
  [(_ e:expr)
   #'e]
  [(_ e:expr rest ...+)
   (syntax/loc #'e
     (>>= e (λ [x] (do rest ...))))])

(defn ap : (∀ [m a b] (Monad m) => {(m {a -> b}) -> (m a) -> (m b)})
  [[mf mx] (do [f <- mf]
               [x <- mx]
               (pure (f x)))])
