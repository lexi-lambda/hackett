#lang hackett/private/kernel

(require (only-in racket/base for-syntax)

         (for-syntax racket/base
                     syntax/parse/class/paren-shape)

         (except-in hackett/private/adt data)
         (except-in hackett/private/class class)
         hackett/private/provide
         syntax/parse/define)

(provide (data Unit) (data Bool) (data Tuple) (data Maybe) (data List)
         not or and if fst snd

         id compose const flip

         (class Functor) (rename-out [map <$>]) <&> <$ $> ignore
         (class Applicative) sequence traverse
         (class Monad) =<< >>= do ap)

;; ---------------------------------------------------------------------------------------------------
;; datatypes

(data Unit unit)
(data Bool true false)
(data (Tuple a b) (tuple a b))
(data (Maybe a) (just a) nothing)
(data (List a)
  {a :: (List a)} #:fixity right
  nil)

(defn not : {Bool -> Bool}
  [[true ] false]
  [[false] true])

(defn or : {Bool -> Bool -> Bool}
  [[true  _] true]
  [[false y] y])

(defn and : {Bool -> Bool -> Bool}
  [[true  y] y]
  [[false _] false])

(defn if : (∀ [a] {Bool -> a -> a -> a})
  [[true  x _] x]
  [[false _ y] y])

(defn fst : (∀ [a b] {(Tuple a b) -> a})
  [[(tuple x _)] x])

(defn snd : (∀ [a b] {(Tuple a b) -> b})
  [[(tuple _ x)] x])

;; ---------------------------------------------------------------------------------------------------
;; function combinators

(defn id : (∀ [a] {a -> a})
  [[x] x])

(defn compose : (∀ [a b c] {{b -> c} -> {a -> b} -> a -> c})
  [[f g x] (f (g x))])

(defn const : (∀ [a b] {a -> b -> a})
  [[x _] x])

(defn flip : (∀ [a b c] {{a -> b -> c} -> b -> a -> c})
  [[f x y] (f y x)])

;; ---------------------------------------------------------------------------------------------------
;; Functor

(class (Functor f)
  [map : (∀ [a b] {{a -> b} -> (f a) -> (f b)})])

(def <&> : (∀ [f a b] (Functor f) => {(f a) -> {a -> b} -> (f b)})
  (flip map))

(def <$ : (∀ [f a b] (Functor f) => {a -> (f b) -> (f a)})
  (compose map const))

(def $> : (∀ [f a b] (Functor f) => {(f b) -> a -> (f a)})
  (flip <$))

(def ignore : (∀ [f a] (Functor f) => {(f a) -> (f Unit)})
  (map (const unit)))

(instance (Functor Maybe)
  [map (λ* [[f (just x)] (just (f x))]
           [[_ nothing ] nothing])])

(instance (Functor List)
  [map (λ* [[f {y :: ys}] {(f y) :: (map f ys)}]
           [[_ nil      ] nil])])

;; ---------------------------------------------------------------------------------------------------
;; Applicative

(class (Functor f) => (Applicative f)
  [pure : (∀ [a] {a -> (f a)})]
  [<*> : (∀ [a b] {(f {a -> b}) -> (f a) -> (f b)})])

(defn sequence : (∀ [f a] (Applicative f) => {(List (f a)) -> (f (List a))})
  [[{y :: ys}] {:: map y <*> (sequence ys)}]
  [[nil      ] (pure nil)])

(defn traverse : (∀ [f a b] (Applicative f) => {{a -> (f b)} -> (List a) -> (f (List b))})
  [[f xs] (sequence (map f xs))])

(instance (Applicative Maybe)
  [pure just]
  [<*> (λ* [[(just f) x] (map f x)]
           [[nothing  _] nothing])])

(instance (Applicative List)
  [pure (λ [x] {x :: nil})]
  [<*> ap])

;; ---------------------------------------------------------------------------------------------------
;; Monad

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

(instance (Monad Maybe)
  [join (λ* [[(just (just x))] (just x)]
            [[_              ] nothing])])

(instance (Monad List)
  [join (λ* [[{{z :: zs} :: yss}] {z :: (join {zs :: yss})}]
            [[{nil       :: yss}] (join yss)]
            [[nil               ] nil])])
