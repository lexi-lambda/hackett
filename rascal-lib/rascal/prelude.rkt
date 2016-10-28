#lang rascal

(provide (all-defined-out))

(data Unit unit)

;; ---------------------------------------------------------------------------------------------------

(def flip : (forall [a b c] (-> (-> a (-> b c))
                                (-> b (-> a c))))
  (λ (f x y) (f y x)))

(def id : (forall [a] (-> a a))
  (λ (x) x))

(def const : (forall [a b] (-> a (-> b a)))
  (λ (y x) y))

;; ---------------------------------------------------------------------------------------------------

(class (Show a)
  [show : (-> a String)])

(instance (Show String)
  [show id])

(instance (Show Integer)
  [show show/Integer])

(instance (Show Unit)
  [show (const "unit")])

;; ---------------------------------------------------------------------------------------------------

(class (Functor f)
  [map : (forall [a b] (-> (-> a b) (-> (f a) (f b))))])

(def <$> : (forall [a b f] (=> [(Functor f)] (-> (-> a b) (-> (f a) (f b)))))
  map)

(def $> : (forall [a b f] (=> [(Functor f)] (-> b (-> (f a) (f b)))))
  (λ (x) (map (const x))))

(class (Applicative f)
  [pure : (forall [a] (-> a (f a)))]
  [<*> : (forall [a b] (-> (f (-> a b)) (-> (f a) (f b))))])

(def *> : (forall [a b f] (=> [(Applicative f)] (-> (f a) (-> (f b) (f b)))))
  (λ (fa fb) {{(pure (λ (_ x) x)) . <*> . fa} . <*> . fb}))

(def <* : (forall [a b f] (=> [(Applicative f)] (-> (f a) (-> (f b) (f a)))))
  (λ (fa fb) {{(pure (λ (x _) x)) . <*> . fa} . <*> . fb}))

(class (Monad m)
  [join : (forall [a] (-> (m (m a)) (m a)))])

(def =<< : (forall [a b m] (=> [(Functor m) (Monad m)]
                               (-> (-> a (m b)) (-> (m a) (m b)))))
  (λ (f m) (join (map f m))))

(def >>= : (forall [a b m] (=> [(Functor m) (Monad m)]
                               (-> (m a) (-> (-> a (m b)) (m b)))))
  (flip =<<))

(def ap : (forall [a b m] (=> [(Applicative m) (Monad m)] (-> (m (-> a b)) (-> (m a) (m b)))))
  (λ (mf mx)
    {mf . >>= . (λ (f) {mx . >>= . (λ (x) (pure (f x)))})}))

;; ---------------------------------------------------------------------------------------------------

(data Bool true false)

(instance (Show Bool)
  [show (λ (x) (case x
                 [true "true"]
                 [false "false"]))])

(def not : (-> Bool Bool)
  (λ (x) (case x [true false]
           [false true])))

;; ---------------------------------------------------------------------------------------------------

(data (Maybe a)
  (just a)
  nothing)

(instance (forall [a] (=> [(Show a)] (Show (Maybe a))))
  [show (λ (x) (case x
                 [(just v) (string-append "(just " (string-append (show v) ")"))]
                 [nothing "nothing"]))])

(def maybe : (forall [a b] (-> b (-> (-> a b) (-> (Maybe a) b))))
  (λ (x f m)
    (case m
      [(just v) (f v)]
      [nothing  x])))

(instance (Functor Maybe)
  [map (λ (f m) (case m
                  [(just x) (just (f x))]
                  [nothing  nothing]))])

(instance (Applicative Maybe)
  [pure just]
  [<*> (λ (mf ma)
         (case mf
           [(just f) (case ma
                       [(just a) (just (f a))]
                       [nothing  nothing])]
           [nothing  nothing]))])

(instance (Monad Maybe)
  [join (λ (m) (case m
                 [(just (just x)) (just x)]
                 [_               nothing]))])

;; ---------------------------------------------------------------------------------------------------

(data (Either a b)
  (left a)
  (right b))

(instance (forall [a b] (=> [(Show a) (Show b)] (Show (Either a b))))
  [show (λ (x) (case x
                 [(left v) (string-append "(left " (string-append (show v) ")"))]
                 [(right v) (string-append "(right " (string-append (show v) ")"))]))])

(def either : (forall [a b c] (-> (-> a c) (-> (-> b c) (-> (Either a b) c))))
  (λ (f g e) (case e
               [(right x) (f x)]
               [(left x)  (g x)])))

(instance (forall [e] (Functor (Either e)))
  [map (λ (f e) (case e
                  [(right x) (right (f x))]
                  [(left x)  (left x)]))])

(instance (forall [e] (Applicative (Either e)))
  [pure right]
  [<*> (λ (ef ea)
         (case ef
           [(right f) (case ea
                        [(right a) (right (f a))]
                        [(left e)  (left e)])]
           [(left e)  (left e)]))])

(instance (forall [e] (Monad (Either e)))
  [join (λ (e) (case e
                 [(right (right x)) (right x)]
                 [(right (left e))  (left e)]
                 [(left e)          (left e)]))])

;; ---------------------------------------------------------------------------------------------------

(data (List a)
  (cons a (List a))
  nil)

(instance (forall [a] (=> [(Show a)] (Show (List a))))
  [show (λ (x) (case x
                 [(cons v vs) (string-append
                               "(cons " (string-append (show v) (string-append (show vs) ")")))]
                 [nil "nil"]))])

(def foldl : (forall [a b] (-> (-> b (-> a b)) (-> b (-> (List a) b))))
  (λ (f acc lst)
    (case lst
      [nil acc]
      [(cons x xs) (foldl f (f acc x) xs)])))

(def reverse : (forall [a] (-> (List a) (List a)))
  (foldl (flip cons) nil))

(instance (Functor List)
  [map (λ (f) (foldl (λ (acc x) (cons (f x) acc)) nil))])
