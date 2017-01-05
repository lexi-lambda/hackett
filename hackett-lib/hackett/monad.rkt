#lang hackett/private/kernel

(require (only-in racket/base for-syntax))

(require (for-syntax racket/base)
         hackett/function
         syntax/parse/define)

(provide (class Functor) $>
         (class Applicative) *> <*
         (class Monad) do =<< >>= ap
         (rename [map <$>]))

;; ---------------------------------------------------------------------------------------------------
;; Functor

(class (Functor f)
  [map : (forall [a b] (-> (-> a b) (-> (f a) (f b))))])

(def $> : (forall [a b f] (Functor f) => (-> b (-> (f a) (f b))))
  (λ (x) (map (const x))))

;; ---------------------------------------------------------------------------------------------------
;; Applicative

(class (Applicative f)
  [pure : (forall [a] (-> a (f a)))]
  [<*> : (forall [a b] (-> (f (-> a b)) (-> (f a) (f b))))])

(def *> : (forall [a b f] (Applicative f) => (-> (f a) (-> (f b) (f b))))
  (λ (fa fb) {(pure (λ (_ x) x)) <*> fa <*> fb}))

(def <* : (forall [a b f] (Applicative f) => (-> (f a) (-> (f b) (f a))))
  (λ (fa fb) {(pure (λ (x _) x)) <*> fa <*> fb}))

;; ---------------------------------------------------------------------------------------------------
;; Monad

(class (Monad m)
  [join : (forall [a] (-> (m (m a)) (m a)))])

(def =<< : (forall [a b m] (Functor m) (Monad m) => (-> (-> a (m b)) (-> (m a) (m b))))
  (λ (f m) (join (map f m))))

(def >>= : (forall [a b m] (Functor m) (Monad m) => (-> (m a) (-> (-> a (m b)) (m b))))
  (flip =<<))

(define-syntax-parser do
  #:literals [: <- def]
  [(_ e:expr)
   #'e]
  [(_ [x:id <- ~! e:expr] rest ...+)
   #'{e >>= (λ (x) (do rest ...))}]
  [(_ (def ~! x:id : τ:expr e:expr) ...+ rest ...+)
   #'(letrec ([x : τ e] ...)
       (do rest ...))]
  [(_ e:expr rest ...+)
   #'{e *> (do rest ...)}])

(def ap : (forall [a b m] (Applicative m) (Monad m) => (-> (m (-> a b)) (-> (m a) (m b))))
  (λ (mf mx) (do [f <- mf]
                 [x <- mx]
                 (pure (f x)))))
