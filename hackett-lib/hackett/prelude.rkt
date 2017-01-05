#lang hackett/base

(require (only-in racket/base for-syntax)
         (only-in racket/require multi-in))

(require (for-syntax racket/base)
         (multi-in hackett [data/bool data/unit function monad semigroup])
         (only-in hackett/private/prim
                  IO main print!
                  + - * < > <= >= quotient! remainder!
                  equal?/Integer show/Integer
                  equal?/String)
         syntax/parse/define)

(provide (all-defined-out)
         (all-from-out hackett/data/bool)
         (all-from-out hackett/data/unit)
         (all-from-out hackett/function)
         (all-from-out hackett/monad)
         (all-from-out hackett/semigroup)
         IO main print!
         + - * < > <= >= quotient! remainder! quotient remainder
         (rename [equal? =]))

;; ---------------------------------------------------------------------------------------------------

(class (Eq a)
  [equal? : {a -> {a -> Bool}}])

(instance (Eq Integer)
  [equal? equal?/Integer])

(instance (Eq String)
  [equal? equal?/String])

(instance (Eq Bool)
  [equal? (λ (x y) (case x [true  y]
                           [false (not y)]))])

(instance (Eq Unit)
  [equal? (λ (_ _) true)])

;; ---------------------------------------------------------------------------------------------------

(class (Show a)
  [show : (-> a String)])

(instance (Show String)
  [show (λ (x) {"\"" <> x <> "\""})])

(instance (Show Integer)
  [show show/Integer])

(instance (Show Bool)
  [show (λ (x) (case x
                 [true "true"]
                 [false "false"]))])

(instance (Show Unit)
  [show (const "unit")])

(def println! : {String -> (IO Unit)}
  (λ (x) (do (print! x)
             (print! "\n"))))

(def show! : (forall [a] (Show a) => {a -> (IO Unit)})
  (λ (x) (println! (show x))))

;; ---------------------------------------------------------------------------------------------------

(data (Maybe a)
  (just a)
  nothing)

(instance (forall [a] (Eq a) => (Eq (Maybe a)))
  [equal? (λ (x y) (case x
                     [(just a) (case y
                                 [(just b) (equal? a b)]
                                 [nothing  false])]
                     [nothing  (case y
                                 [(just _) false]
                                 [nothing  true])]))])

(instance (forall [a] (Show a) => (Show (Maybe a)))
  [show (λ (x) (case x
                 [(just v) {"(just " <> (show v) <> ")"}]
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

(def quotient : {Integer -> {Integer -> (Maybe Integer)}}
  (λ (x y) (case (equal? y 0)
             [true  nothing]
             [false (just (quotient! x y))])))

(def remainder : {Integer -> {Integer -> (Maybe Integer)}}
  (λ (x y) (case (equal? y 0)
             [true  nothing]
             [false (just (remainder! x y))])))

;; ---------------------------------------------------------------------------------------------------

(data (Either a b)
  (left a)
  (right b))

(instance (forall [a b] (Eq a) (Eq b) => (Eq (Either a b)))
  [equal? (λ (x y) (case x
                     [(right a) (case y
                                  [(right b) (equal? a b)]
                                  [(left _)  false])]
                     [(left a)  (case y
                                  [(right _) false]
                                  [(left b)  (equal? a b)])]))])

(instance (forall [a b] (Show a) (Show b) => (Show (Either a b)))
  [show (λ (x) (case x
                 [(left v) {"(left " <> (show v) <> ")"}]
                 [(right v) {"(right " <> {(show v) <> ")"}}]))])

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
  {a :: (List a)}
  nil)

(instance (forall [a] (Eq a) => (Eq (List a)))
  [equal? (λ (x y) (case x
                     [(:: a as) (case y
                                    [(:: b bs) (and (equal? a b)
                                                    (equal? as bs))]
                                    [nil         false])]
                     [nil         (case y
                                    [(:: _ _)  false]
                                    [nil       true])]))])

(instance (forall [a] (Show a) => (Show (List a)))
  [show (λ (x) (case x
                 [(:: v vs) {"{" <> (show v) <> " :: " <> (show vs) <> "}"}]
                 [nil "nil"]))])

(def foldl : (forall [a b] (-> (-> b (-> a b)) (-> b (-> (List a) b))))
  (λ (f acc lst)
    (case lst
      [nil acc]
      [(:: x xs) (foldl f (f acc x) xs)])))

(def foldr : (forall [a b] (-> (-> a (-> b b)) (-> b (-> (List a) b))))
  (λ (f acc lst)
    (case lst
      [nil acc]
      [(:: x xs) (f x (foldr f acc xs))])))

(instance (forall [a] (Semigroup (List a)))
  [append (λ (xs ys) (foldr :: ys xs))])

(def reverse : (forall [a] (-> (List a) (List a)))
  (foldl (flip ::) nil))

(instance (Functor List)
  [map (λ (f) (foldl (λ (acc x) {(f x) :: acc}) nil))])

(instance (Monad List)
  [join (λ (xss) (case xss
                   [nil         nil]
                   [(:: ys yss) (case ys
                                  [nil       (join yss)]
                                  [(:: z zs) {z :: (join {zs :: yss})}])]))])
