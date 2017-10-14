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
  [[true ] false]
  [[false] true])

(defn || : {Bool -> Bool -> Bool} #:fixity 2 right
  [[true  _] true]
  [[false y] y])

(defn && : {Bool -> Bool -> Bool} #:fixity 2 right
  [[true  y] y]
  [[false _] false])

(defn if : (∀ [a] {Bool -> a -> a -> a})
  [[true  x _] x]
  [[false _ y] y])

(defn fst : (∀ [a b] {(Tuple a b) -> a})
  [[(tuple x _)] x])

(defn snd : (∀ [a b] {(Tuple a b) -> b})
  [[(tuple _ x)] x])

(defn foldr : (∀ [a b] {{a -> b -> b} -> b -> (List a) -> b})
  [[f a {x :: xs}] (f x (foldr f a xs))]
  [[_ a nil      ] a])

(defn unsafe-run-io! : (∀ [a] {(IO a) -> a})
  [[(io f)] (snd (f real-world))])

;; ---------------------------------------------------------------------------------------------------
;; function combinators

(defn id : (∀ [a] {a -> a})
  [[x] x])

(defn . : (∀ [a b c] {{b -> c} -> {a -> b} -> a -> c}) #:fixity 9 right
  [[f g x] (f (g x))])

(defn $ : (∀ [a b] {{a -> b} -> a -> b}) #:fixity 0 right
  [[f x] (f x)])

(defn & : (∀ [a b] {a -> {a -> b} -> b}) #:fixity 0 left
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
  [show (λ [unit] "unit")])

(instance (Show Bool)
  [show (λ* [[true ] "true"]
            [[false] "false"])])

(instance (Show Integer)
  [show show/Integer])

(instance (Show Double)
  [show show/Double])

(instance (Show String)
  [show (λ [str] {"\"" ++ str ++ "\""})])

(instance (∀ [a] (Show a) => (Show (Maybe a)))
  [show (λ* [[(just x)] {"(just " ++ (show x) ++ ")"}]
            [[nothing ] "nothing"])])

(instance (∀ [a b] (Show a) (Show b) => (Show (Either a b)))
  [show (λ* [[(left x)] {"(left " ++ (show x) ++ ")"}]
            [[(right x)] {"(right " ++ (show x) ++ ")"}])])

(instance (∀ [a b] (Show a) (Show b) => (Show (Tuple a b)))
  [show (λ [(tuple a b)] {"(tuple " ++ (show a) ++ " " ++ (show b) ++ ")"})])

(instance (∀ [a] (Show a) => (Show (List a)))
  [show (λ* [[nil] "nil"]
            [[xs] (let ([strs (map {(λ [x] {x ++ " :: "}) . show} xs)])
                    {"{" ++ (concat strs) ++ "nil}"})])])

;; ---------------------------------------------------------------------------------------------------
;; Eq

(class (Eq a)
  [== : {a -> a -> Bool} #:fixity 4 left])

(instance (Eq Unit)
  [== (λ [unit unit] true)])

(instance (Eq Bool)
  [== (λ* [[true  y] y]
          [[false y] (not y)])])

(instance (Eq Integer)
  [== equal?/Integer])

(instance (Eq Double)
  [== equal?/Double])

(instance (Eq String)
  [== equal?/String])

(instance (∀ [a] (Eq a) => (Eq (Maybe a)))
  [== (λ* [[(just a) (just b)] {a == b}]
          [[nothing  nothing ] true]
          [[_        _       ] false])])

(instance (∀ [a b] (Eq a) (Eq b) => (Eq (Either a b)))
  [== (λ* [[(right a) (right b)] {a == b}]
          [[(left  a) (left  b)] {a == b}]
          [[_         _        ] false])])

(instance (∀ [a b] (Eq a) (Eq b) => (Eq (Tuple a b)))
  [== (λ [(tuple a b) (tuple c d)] {{a == c} && {b == d}})])

(instance (∀ [a] (Eq a) => (Eq (List a)))
  [== (λ* [[{x :: xs} {y :: ys}] {{x == y} && {xs == ys}}]
          [[nil       nil      ] true]
          [[_         _        ] false])])

;; ---------------------------------------------------------------------------------------------------
;; Semigroup / Monoid

(class (Semigroup a)
  [++ : {a -> a -> a} #:fixity 5 right])

(instance (Semigroup String)
  [++ append/String])

(instance (∀ [a] (Semigroup a) => (Semigroup (Maybe a)))
  [++ (λ* [[(just x) (just y)] (just {x ++ y})]
          [[(just x) nothing ] (just x)]
          [[nothing  (just y)] (just y)]
          [[nothing  nothing ] nothing])])

(instance (∀ [a] (Semigroup (List a)))
  [++ (λ* [[{z :: zs} ys] {z :: {zs ++ ys}}]
          [[nil       ys] ys])])

(instance (∀ [a b] (Semigroup b) => (Semigroup {a -> b}))
  [++ (λ [f g x] {(f x) ++ (g x)})])

(class (Semigroup a) => (Monoid a)
  [mempty : a])

(instance (Monoid String)
  [mempty ""])

(instance (∀ [a] (Semigroup a) => (Monoid (Maybe a)))
  [mempty nothing])

(instance (∀ [a] (Monoid (List a)))
  [mempty nil])

(instance (∀ [a b] (Monoid b) => (Monoid {a -> b}))
  [mempty (λ [_] mempty)])

(def concat : (∀ [a] (Monoid a) => {(List a) -> a})
  (foldr ++ mempty))

;; ---------------------------------------------------------------------------------------------------
;; Functor

(class (Functor f)
  [map : (∀ [a b] {{a -> b} -> (f a) -> (f b)}) #:fixity 4 left])

(def <&> : (∀ [f a b] (Functor f) => {(f a) -> {a -> b} -> (f b)}) #:fixity 4 left
  (flip map))

(def <$ : (∀ [f a b] (Functor f) => {a -> (f b) -> (f a)}) #:fixity 4 left
  {map . const})

(def $> : (∀ [f a b] (Functor f) => {(f b) -> a -> (f a)}) #:fixity 4 left
  (flip <$))

(def ignore : (∀ [f a] (Functor f) => {(f a) -> (f Unit)})
  (map (const unit)))

(instance (Functor Maybe)
  [map (λ* [[f (just x)] (just (f x))]
           [[_ nothing ] nothing])])

(instance (∀ [e] (Functor (Either e)))
  [map (λ* [[f (right x)] (right (f x))]
           [[_ (left  x)] (left  x)])])

(instance (Functor List)
  [map (λ* [[f {y :: ys}] {(f y) :: (map f ys)}]
           [[_ nil      ] nil])])

(instance (Functor IO)
  [map (λ [f (io mx)]
         (io (λ [rw]
               (case (mx rw)
                 [(tuple rw* a) (tuple rw* (f a))]))))])

;; ---------------------------------------------------------------------------------------------------
;; Applicative

(class (Functor f) => (Applicative f)
  [pure : (∀ [a] {a -> (f a)})]
  [<*> : (∀ [a b] {(f {a -> b}) -> (f a) -> (f b)}) #:fixity 4 left])

(defn sequence : (∀ [f a] (Applicative f) => {(List (f a)) -> (f (List a))})
  [[{y :: ys}] {:: map y <*> (sequence ys)}]
  [[nil      ] (pure nil)])

(defn traverse : (∀ [f a b] (Applicative f) => {{a -> (f b)} -> (List a) -> (f (List b))})
  [[f xs] (sequence (map f xs))])

(instance (Applicative Maybe)
  [pure just]
  [<*> (λ* [[(just f) x] (map f x)]
           [[nothing  _] nothing])])

(instance (∀ [e] (Applicative (Either e)))
  [pure right]
  [<*> (λ* [[(right f) x] (map f x)]
           [[(left  x) _] (left x)])])

(instance (Applicative List)
  [pure (λ [x] {x :: nil})]
  [<*> ap])

(instance (Applicative IO)
  [pure (λ [x] (io (λ [rw] (tuple rw x))))]
  [<*> ap])

;; ---------------------------------------------------------------------------------------------------
;; Monad

(class (Applicative m) => (Monad m)
  [join : (∀ [a] {(m (m a)) -> (m a)})])

(defn =<< : (∀ [m a b] (Monad m) => {{a -> (m b)} -> (m a) -> (m b)}) #:fixity 1 right
  [[f x] (join (map f x))])

(def >>= : (∀ [m a b] (Monad m) => {(m a) -> {a -> (m b)} -> (m b)}) #:fixity 1 left
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

(defn ap : (∀ [m a b] (Monad m) => {(m {a -> b}) -> (m a) -> (m b)}) #:fixity 4 left
  [[mf mx] (do [f <- mf]
               [x <- mx]
               (pure (f x)))])

(instance (Monad Maybe)
  [join (λ* [[(just (just x))] (just x)]
            [[_              ] nothing])])

(instance (∀ [e] (Monad (Either e)))
  [join (λ* [[(right (right x))] (right x)]
            [[(right (left  x))] (left  x)]
            [[(left  x)        ] (left  x)])])

(instance (Monad List)
  [join (λ* [[{{z :: zs} :: yss}] {z :: (join {zs :: yss})}]
            [[{nil       :: yss}] (join yss)]
            [[nil               ] nil])])

(instance (Monad IO)
  [join (λ [(io outer)]
          (io (λ [rw]
                (case (outer rw)
                  [(tuple rw* m-inner)
                   (case m-inner
                     [(io inner)
                      (inner rw*)])]))))])
