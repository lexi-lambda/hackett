#lang hackett/private/kernel

(require (only-in racket/base for-syntax)

         (for-syntax racket/base
                     syntax/parse/class/paren-shape)

         (except-in hackett/private/adt data)
         (except-in hackett/private/class class)
         hackett/private/provide
         hackett/private/prim/op
         hackett/private/prim/type
         syntax/parse/define)

(provide not || && if fst snd foldr unsafe-run-io!

         . $ & id const flip

         (class Eq) (class Show)
         (class Semigroup) (class Monoid) concat

         (class Functor) (rename-out [map <$>]) <&> <$ $> ignore
         (class Applicative) sequence traverse
         (class Monad) =<< >>= do ap)

;; ---------------------------------------------------------------------------------------------------
;; basic operations

(defn not : {Bool -> Bool}
  [[True ] False]
  [[False] True])

(defn || : {Bool -> Bool -> Bool} #:fixity right
  [[True  _] True]
  [[False y] y])

(defn && : {Bool -> Bool -> Bool} #:fixity right
  [[True  y] y]
  [[False _] False])

(defn if : (∀ [a] {Bool -> a -> a -> a})
  [[True  x _] x]
  [[False _ y] y])

(defn fst : (∀ [a b] {(Tuple a b) -> a})
  [[(Tuple x _)] x])

(defn snd : (∀ [a b] {(Tuple a b) -> b})
  [[(Tuple _ x)] x])

(defn foldr : (∀ [a b] {{a -> b -> b} -> b -> (List a) -> b})
  [[f a {x :: xs}] (f x (foldr f a xs))]
  [[_ a Nil      ] a])

(defn unsafe-run-io! : (∀ [a] {(IO a) -> a})
  [[(IO f)] (snd (f Real-World))])

;; ---------------------------------------------------------------------------------------------------
;; function combinators

(defn id : (∀ [a] {a -> a})
  [[x] x])

(defn . : (∀ [a b c] {{b -> c} -> {a -> b} -> a -> c})
  [[f g x] (f (g x))])

(defn $ : (∀ [a b] {{a -> b} -> a -> b})
  [[f x] (f x)])

(defn & : (∀ [a b] {a -> {a -> b} -> b})
  [[x f] (f x)])

(defn const : (∀ [a b] {a -> b -> a})
  [[x _] x])

(defn flip : (∀ [a b c] {{a -> b -> c} -> b -> a -> c})
  [[f x y] (f y x)])

;; ---------------------------------------------------------------------------------------------------
;; Show

(class (Show a)
  [show : {a -> String}])

(instance (Show Unit)
  [show (λ [Unit] "Unit")])

(instance (Show Bool)
  [show (λ* [[True ] "True"]
            [[False] "False"])])

(instance (Show Integer)
  [show show/Integer])

(instance (Show Double)
  [show show/Double])

(instance (Show String)
  [show (λ [str] {"\"" ++ str ++ "\""})])

(instance (∀ [a] (Show a) => (Show (Maybe a)))
  [show (λ* [[(Just x)] {"(Just " ++ (show x) ++ ")"}]
            [[Nothing ] "Nothing"])])

(instance (∀ [a b] (Show a) (Show b) => (Show (Either a b)))
  [show (λ* [[(Left x)] {"(Left " ++ (show x) ++ ")"}]
            [[(Right x)] {"(Right " ++ (show x) ++ ")"}])])

(instance (∀ [a b] (Show a) (Show b) => (Show (Tuple a b)))
  [show (λ [(Tuple a b)] {"(Tuple " ++ (show a) ++ " " ++ (show b) ++ ")"})])

(instance (∀ [a] (Show a) => (Show (List a)))
  [show (λ* [[Nil] "Nil"]
            [[xs] (let ([strs (map {(λ [x] {x ++ " :: "}) . show} xs)])
                    {"{" ++ (concat strs) ++ "Nil}"})])])

;; ---------------------------------------------------------------------------------------------------
;; Eq

(class (Eq a)
  [== : {a -> a -> Bool}])

(instance (Eq Unit)
  [== (λ [Unit Unit] True)])

(instance (Eq Bool)
  [== (λ* [[True  y] y]
          [[False y] (not y)])])

(instance (Eq Integer)
  [== equal?/Integer])

(instance (Eq Double)
  [== equal?/Double])

(instance (Eq String)
  [== equal?/String])

(instance (∀ [a] (Eq a) => (Eq (Maybe a)))
  [== (λ* [[(Just a) (Just b)] {a == b}]
          [[Nothing  Nothing ] True]
          [[_        _       ] False])])

(instance (∀ [a b] (Eq a) (Eq b) => (Eq (Either a b)))
  [== (λ* [[(Right a) (Right b)] {a == b}]
          [[(Left  a) (Left  b)] {a == b}]
          [[_         _        ] False])])

(instance (∀ [a b] (Eq a) (Eq b) => (Eq (Tuple a b)))
  [== (λ [(Tuple a b) (Tuple c d)] {{a == c} && {b == d}})])

(instance (∀ [a] (Eq a) => (Eq (List a)))
  [== (λ* [[{x :: xs} {y :: ys}] {{x == y} && {xs == ys}}]
          [[Nil       Nil      ] True]
          [[_         _        ] False])])

;; ---------------------------------------------------------------------------------------------------
;; Semigroup / Monoid

(class (Semigroup a)
  [++ : {a -> a -> a}
      #:fixity right])

(instance (Semigroup String)
  [++ append/String])

(instance (∀ [a] (Semigroup a) => (Semigroup (Maybe a)))
  [++ (λ* [[(Just x) (Just y)] (Just {x ++ y})]
          [[(Just x) Nothing ] (Just x)]
          [[Nothing  (Just y)] (Just y)]
          [[Nothing  Nothing ] Nothing])])

(instance (∀ [a] (Semigroup (List a)))
  [++ (λ* [[{z :: zs} ys] {z :: {zs ++ ys}}]
          [[Nil       ys] ys])])

(instance (∀ [a b] (Semigroup b) => (Semigroup {a -> b}))
  [++ (λ [f g x] {(f x) ++ (g x)})])

(class (Semigroup a) => (Monoid a)
  [mempty : a])

(instance (Monoid String)
  [mempty ""])

(instance (∀ [a] (Semigroup a) => (Monoid (Maybe a)))
  [mempty Nothing])

(instance (∀ [a] (Monoid (List a)))
  [mempty Nil])

(instance (∀ [a b] (Monoid b) => (Monoid {a -> b}))
  [mempty (λ [_] mempty)])

(def concat : (∀ [a] (Monoid a) => {(List a) -> a})
  (foldr ++ mempty))

;; ---------------------------------------------------------------------------------------------------
;; Functor

(class (Functor f)
  [map : (∀ [a b] {{a -> b} -> (f a) -> (f b)})])

(def <&> : (∀ [f a b] (Functor f) => {(f a) -> {a -> b} -> (f b)})
  (flip map))

(def <$ : (∀ [f a b] (Functor f) => {a -> (f b) -> (f a)})
  {map . const})

(def $> : (∀ [f a b] (Functor f) => {(f b) -> a -> (f a)})
  (flip <$))

(def ignore : (∀ [f a] (Functor f) => {(f a) -> (f Unit)})
  (map (const Unit)))

(instance (Functor Maybe)
  [map (λ* [[f (Just x)] (Just (f x))]
           [[_ Nothing ] Nothing])])

(instance (∀ [e] (Functor (Either e)))
  [map (λ* [[f (Right x)] (Right (f x))]
           [[_ (Left  x)] (Left  x)])])

(instance (Functor List)
  [map (λ* [[f {y :: ys}] {(f y) :: (map f ys)}]
           [[_ Nil      ] Nil])])

(instance (Functor IO)
  [map (λ [f (IO mx)]
         (IO (λ [rw]
               (case (mx rw)
                 [(Tuple rw* a) (Tuple rw* (f a))]))))])

;; ---------------------------------------------------------------------------------------------------
;; Applicative

(class (Functor f) => (Applicative f)
  [pure : (∀ [a] {a -> (f a)})]
  [<*> : (∀ [a b] {(f {a -> b}) -> (f a) -> (f b)})])

(defn sequence : (∀ [f a] (Applicative f) => {(List (f a)) -> (f (List a))})
  [[{y :: ys}] {:: map y <*> (sequence ys)}]
  [[Nil      ] (pure Nil)])

(defn traverse : (∀ [f a b] (Applicative f) => {{a -> (f b)} -> (List a) -> (f (List b))})
  [[f xs] (sequence (map f xs))])

(instance (Applicative Maybe)
  [pure Just]
  [<*> (λ* [[(Just f) x] (map f x)]
           [[Nothing  _] Nothing])])

(instance (∀ [e] (Applicative (Either e)))
  [pure Right]
  [<*> (λ* [[(Right f) x] (map f x)]
           [[(Left  x) _] (Left x)])])

(instance (Applicative List)
  [pure (λ [x] {x :: Nil})]
  [<*> ap])

(instance (Applicative IO)
  [pure (λ [x] (IO (λ [rw] (Tuple rw x))))]
  [<*> ap])

;; ---------------------------------------------------------------------------------------------------
;; Monad

(class (Applicative m) => (Monad m)
  [join : (∀ [a] {(m (m a)) -> (m a)})
        (λ [x] {id =<< x})]
  [=<< : (∀ [a b] {{a -> (m b)} -> (m a) -> (m b)})
       (λ [f x] (join (map f x)))])

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
  [join (λ* [[(Just (Just x))] (Just x)]
            [[_              ] Nothing])])

(instance (∀ [e] (Monad (Either e)))
  [join (λ* [[(Right (Right x))] (Right x)]
            [[(Right (Left  x))] (Left  x)]
            [[(Left  x)        ] (Left  x)])])

(instance (Monad List)
  [join (λ* [[{{z :: zs} :: yss}] {z :: (join {zs :: yss})}]
            [[{Nil       :: yss}] (join yss)]
            [[Nil               ] Nil])])

(instance (Monad IO)
  [join (λ [(IO outer)]
          (IO (λ [rw]
                (case (outer rw)
                  [(Tuple rw* m-inner)
                   (case m-inner
                     [(IO inner)
                      (inner rw*)])]))))])
