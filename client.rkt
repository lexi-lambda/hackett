#lang rascal

(data Unit unit)

(data Bool
  true
  false)

(data (Maybe a)
  (just a)
  nothing)

(class (Show a)
  [show : (→ a String)])

(class (Functor f)
  [map : (∀ [a b] (→ (→ a b) (→ (f a) (f b))))])

(class (Monad m)
  [pure : (∀ [a] (→ a (m a)))]
  [join : (∀ [a] (→ (m (m a)) (m a)))])

(instance (Functor Maybe)
  [map (λ (f x)
         (case x
           [(just v) (just (f v))]
           [nothing nothing]))])

(instance (Monad Maybe)
  [pure just]
  [join (λ (x)
          (case x
            [(just (just v)) (just v)]
            [_               nothing]))])

(letrec ([>>= : (∀ [m a b] (⇒ [(Functor m) (Monad m)] (→ (m a) (→ (→ a (m b)) (m b)))))
              (λ (m f) (join (map f m)))]
         [x : (⇒ [] (Maybe Integer))
            (map (+ 1) (just 3))]
         [y : (⇒ [] (Maybe Integer))
            (>>= x (λ (v) (just v)))])
  y)

#;(instance (Show String)
  [show (λ (x) x)])

#;(instance (Show Integer)
  [show show/Integer])

(instance (Show Bool)
  [show (λ (x) (case x
                 [true "true"]
                 [false "false"]))])

#;(instance (∀ [a] (⇒ [(Show a)] (Show (Maybe a))))
  [show (λ (x) (case x
                 [(just v) (string-append (string-append "(just " (show v)) ")")]
                 [nothing "nothing"]))])

#;(letrec ([show/label : (∀ [a] (⇒ [(Show a)] (→ a String)))
                     (λ (x) (string-append "showing: " (show x)))])
  (show/label 1))

(letrec ([x : (⇒ [] String)
            (show true)])
  x)

#;(letrec ([main : (→ Integer String)
               (λ (x) (show (+ x 1)))])
  main)
