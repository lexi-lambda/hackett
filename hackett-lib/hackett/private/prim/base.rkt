#lang hackett/private/kernel

(require (only-in racket/base for-syntax)

         (for-syntax racket/base
                     syntax/parse/class/paren-shape

                     hackett/private/typecheck
                     hackett/private/util/stx)

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

(defn if : (forall [a] {Bool -> a -> a -> a})
  [[True  x _] x]
  [[False _ y] y])

(defn fst : (forall [a b] {(Tuple a b) -> a})
  [[(Tuple x _)] x])

(defn snd : (forall [a b] {(Tuple a b) -> b})
  [[(Tuple _ x)] x])

(defn foldr : (forall [a b] {{a -> b -> b} -> b -> (List a) -> b})
  [[f a {x :: xs}] (f x (foldr f a xs))]
  [[_ a Nil      ] a])

(defn unsafe-run-io! : (forall [a] {(IO a) -> a})
  [[(IO f)] (snd (f Real-World))])

;; ---------------------------------------------------------------------------------------------------
;; function combinators

(defn id : (forall [a] {a -> a})
  [[x] x])

(defn . : (forall [a b c] {{b -> c} -> {a -> b} -> a -> c})
  [[f g x] (f (g x))])

(defn $ : (forall [a b] {{a -> b} -> a -> b})
  [[f x] (f x)])

(defn & : (forall [a b] {a -> {a -> b} -> b})
  [[x f] (f x)])

(defn const : (forall [a b] {a -> b -> a})
  [[x _] x])

(defn flip : (forall [a b c] {{a -> b -> c} -> b -> a -> c})
  [[f x y] (f y x)])

;; ---------------------------------------------------------------------------------------------------
;; Show

(class (Show a)
  [show : {a -> String}]
  #:deriving-transformer
  (syntax-parser
    [(_ _ {~type ty-con:type-constructor-val})
     #:with [data-con:data-constructor-val ...] (attribute ty-con.data-constructors)
     #:with [ty-con-var-id ...] (build-list (attribute ty-con.arity) generate-bound-temporary)
     #:with [[data-con-field-ty ...] ...]
            (for/list ([con-type (in-list (attribute data-con.type))])
              (data-constructor-field-types (attribute ty-con-var-id) con-type))
     #:with [case-clause ...]
            (for/list ([con-id (in-list (attribute data-con))]
                       [fields (in-list (attribute data-con-field-ty))])
              (with-syntax ([[field-binding-id ...] (generate-temporaries fields)]
                            [con-str (datum->syntax #'here (symbol->string (syntax-e con-id)))])
                #`[[(#,con-id field-binding-id ...)]
                   #,(if (zero? (length fields))
                         #'con-str
                         #'{"(" ++ con-str {~@ ++ " " ++ (show field-binding-id)} ... ++ ")"})]))
     (syntax-property
      #'(instance (forall [ty-con-var-id ...] (Show data-con-field-ty) ... ...
                          => (Show (ty-con ty-con-var-id ...)))
          [show (λ* case-clause ...)])
      'disappeared-use
      (syntax-local-introduce #'ty-con))]))

(instance (Show Integer) [show show/Integer])
(instance (Show Double) [show show/Double])
(instance (Show String) [show show/String])
(instance (Show Bytes) [show show/Bytes])

(derive-instance Show Unit)
(derive-instance Show Bool)
(derive-instance Show Maybe)
(derive-instance Show Either)
(derive-instance Show Tuple)

(instance (forall [a] (Show a) => (Show (List a)))
  [show (λ* [[Nil] "Nil"]
            [[xs] (let ([strs (map {(λ [x] {x ++ " :: "}) . show} xs)])
                    {"{" ++ (concat strs) ++ "Nil}"})])])

;; ---------------------------------------------------------------------------------------------------
;; Eq

(class (Eq a)
  [== : {a -> a -> Bool}]
  [/= : {a -> a -> Bool}
      (λ [x y] (not {x == y}))]
  #:deriving-transformer
  (syntax-parser
    [(_ _ {~type ty-con:type-constructor-val})
     #:with [data-con:data-constructor-val ...] (attribute ty-con.data-constructors)
     #:with [ty-con-var-id ...] (build-list (attribute ty-con.arity) generate-bound-temporary)
     #:with [[data-con-field-ty ...] ...]
            (for/list ([con-type (in-list (attribute data-con.type))])
              (data-constructor-field-types (attribute ty-con-var-id) con-type))
     #:with [case-clause ...]
            (for/list ([con-id (in-list (attribute data-con))]
                       [fields (in-list (attribute data-con-field-ty))])
              (with-syntax ([[field-binding-id-1 ...] (generate-temporaries fields)]
                            [[field-binding-id-2 ...] (generate-temporaries fields)])
                #`[[(#,con-id field-binding-id-1 ...) (#,con-id field-binding-id-2 ...)]
                   #,(foldr (λ (a b r) #`(&& (== #,a #,b) #,r))
                            #'True
                            (syntax->list #'[field-binding-id-1 ...])
                            (syntax->list #'[field-binding-id-2 ...]))]))
     (syntax-property
      #'(instance (forall [ty-con-var-id ...] (Eq data-con-field-ty) ... ...
                          => (Eq (ty-con ty-con-var-id ...)))
          [== (λ* case-clause ...
                  [[_ _] False])])
      'disappeared-use
      (syntax-local-introduce #'ty-con))]))

(instance (Eq Bool)
  [== (λ* [[True  y] y]
          [[False y] (not y)])])

(instance (Eq Integer) [== equal?/Integer])
(instance (Eq Double) [== equal?/Double])
(instance (Eq String) [== equal?/String])
(instance (Eq Bytes) [== equal?/Bytes])

(derive-instance Eq Unit)
(derive-instance Eq Maybe)
(derive-instance Eq Either)
(derive-instance Eq Tuple)
(derive-instance Eq List)

;; ---------------------------------------------------------------------------------------------------
;; Semigroup / Monoid

(class (Semigroup a)
  [++ : {a -> a -> a}
      #:fixity right])

(instance (Semigroup String) [++ append/String])
(instance (Semigroup Bytes) [++ append/Bytes])

(instance (forall [a] (Semigroup a) => (Semigroup (Maybe a)))
  [++ (λ* [[(Just x) (Just y)] (Just {x ++ y})]
          [[(Just x) Nothing ] (Just x)]
          [[Nothing  (Just y)] (Just y)]
          [[Nothing  Nothing ] Nothing])])

(instance (forall [a] (Semigroup (List a)))
  [++ (λ* [[{z :: zs} ys] {z :: {zs ++ ys}}]
          [[Nil       ys] ys])])

(instance (forall [a b] (Semigroup b) => (Semigroup {a -> b}))
  [++ (λ [f g x] {(f x) ++ (g x)})])

(class (Semigroup a) => (Monoid a)
  [mempty : a])

(instance (Monoid String) [mempty ""])
(instance (Monoid Bytes) [mempty #""])

(instance (forall [a] (Semigroup a) => (Monoid (Maybe a)))
  [mempty Nothing])

(instance (forall [a] (Monoid (List a)))
  [mempty Nil])

(instance (forall [a b] (Monoid b) => (Monoid {a -> b}))
  [mempty (λ [_] mempty)])

(def concat : (forall [a] (Monoid a) => {(List a) -> a})
  (foldr ++ mempty))

;; ---------------------------------------------------------------------------------------------------
;; Functor

(class (Functor f)
  [map : (forall [a b] {{a -> b} -> (f a) -> (f b)})])

(def <&> : (forall [f a b] (Functor f) => {(f a) -> {a -> b} -> (f b)})
  (flip map))

(def <$ : (forall [f a b] (Functor f) => {a -> (f b) -> (f a)})
  {map . const})

(def $> : (forall [f a b] (Functor f) => {(f b) -> a -> (f a)})
  (flip <$))

(def ignore : (forall [f a] (Functor f) => {(f a) -> (f Unit)})
  (map (const Unit)))

(instance (Functor Maybe)
  [map (λ* [[f (Just x)] (Just (f x))]
           [[_ Nothing ] Nothing])])

(instance (forall [e] (Functor (Either e)))
  [map (λ* [[f (Right x)] (Right (f x))]
           [[_ (Left  x)] (Left  x)])])

(instance (Functor List)
  [map (λ* [[f {y :: ys}] {(f y) :: (map f ys)}]
           [[_ Nil      ] Nil])])

(instance (forall [r] (Functor (-> r)))
  [map .])

(instance (Functor IO)
  [map (λ [f (IO mx)]
         (IO (λ [rw]
               (case (mx rw)
                 [(Tuple rw* a) (Tuple rw* (f a))]))))])

;; ---------------------------------------------------------------------------------------------------
;; Applicative

(class (Functor f) => (Applicative f)
  [pure : (forall [a] {a -> (f a)})]
  [<*> : (forall [a b] {(f {a -> b}) -> (f a) -> (f b)})])

(defn sequence : (forall [f a] (Applicative f) => {(List (f a)) -> (f (List a))})
  [[{y :: ys}] {:: map y <*> (sequence ys)}]
  [[Nil      ] (pure Nil)])

(defn traverse : (forall [f a b] (Applicative f) => {{a -> (f b)} -> (List a) -> (f (List b))})
  [[f xs] (sequence (map f xs))])

(instance (Applicative Maybe)
  [pure Just]
  [<*> (λ* [[(Just f) x] (map f x)]
           [[Nothing  _] Nothing])])

(instance (forall [e] (Applicative (Either e)))
  [pure Right]
  [<*> (λ* [[(Right f) x] (map f x)]
           [[(Left  x) _] (Left x)])])

(instance (Applicative List)
  [pure (λ [x] {x :: Nil})]
  [<*> ap])

(instance (forall [r] (Applicative (-> r)))
  [pure const]
  [<*> (λ [f g x] (f x (g x)))])

(instance (Applicative IO)
  [pure (λ [x] (IO (λ [rw] (Tuple rw x))))]
  [<*> ap])

;; ---------------------------------------------------------------------------------------------------
;; Monad

(class (Applicative m) => (Monad m)
  [join : (forall [a] {(m (m a)) -> (m a)})
        (λ [x] {id =<< x})]
  [=<< : (forall [a b] {{a -> (m b)} -> (m a) -> (m b)})
       (λ [f x] (join (map f x)))])

(def >>= : (forall [m a b] (Monad m) => {(m a) -> {a -> (m b)} -> (m b)})
  (flip =<<))

(define-syntax-parser do
  #:literals [let letrec]
  #:datum-literals [<-]
  [(_ {~and form ({~and form-id {~or let letrec}} ~! binding-pair ...)} rest ...+)
   (syntax/loc #'form
     (form-id (binding-pair ...) (do rest ...)))]
  [(_ {~and clause [~brackets ~! x:id <- e:expr]} rest ...+)
   (syntax/loc #'clause
     (>>= e (λ [x] (do rest ...))))]
  [(_ e:expr)
   #'e]
  [(_ e:expr rest ...+)
   (syntax/loc #'e
     (>>= e (λ [_] (do rest ...))))])

(defn ap : (forall [m a b] (Monad m) => {(m {a -> b}) -> (m a) -> (m b)})
  [[mf mx] (do [f <- mf]
               [x <- mx]
               (pure (f x)))])

(instance (Monad Maybe)
  [join (λ* [[(Just (Just x))] (Just x)]
            [[_              ] Nothing])])

(instance (forall [e] (Monad (Either e)))
  [join (λ* [[(Right (Right x))] (Right x)]
            [[(Right (Left  x))] (Left  x)]
            [[(Left  x)        ] (Left  x)])])

(instance (Monad List)
  [join (λ* [[{{z :: zs} :: yss}] {z :: (join {zs :: yss})}]
            [[{Nil       :: yss}] (join yss)]
            [[Nil               ] Nil])])

(instance (forall [r] (Monad (-> r)))
  [join (λ [f x] (f x x))]
  [=<< (λ [f g x] (f (g x) x))])

(instance (Monad IO)
  [join (λ [(IO outer)]
          (IO (λ [rw]
                (case (outer rw)
                  [(Tuple rw* m-inner)
                   (case m-inner
                     [(IO inner)
                      (inner rw*)])]))))])
