#lang hackett/private/kernel

(require (only-in racket/base all-from-out)

         (except-in hackett/private/adt data)
         (except-in hackett/private/class class)

         hackett/data/list
         hackett/data/maybe
         hackett/monoid
         hackett/semigroup

         hackett/private/prim
         hackett/private/provide)

(provide (all-from-out hackett/data/list)
         (all-from-out hackett/data/maybe)
         (all-from-out hackett/monoid)
         (all-from-out hackett/semigroup)

         (data Unit) (data Bool) (data Tuple) (data Maybe) (data List)
         not or and if fst snd

         id compose const flip

         (class Functor) (rename-out [map <$>]) <&> <$ $> ignore
         (class Applicative) sequence traverse
         (class Monad) =<< >>= do ap

         seq error! undefined!
         IO main print println
         + - * quotient! remainder! < > <= >=
         string-length string-split

         (class Show)
         (class Eq))

;; ---------------------------------------------------------------------------------------------------

(def undefined! : (∀ [a] a)
  (error! "undefined!"))

(defn println : {String -> (IO Unit)}
  [[str] (do (print str)
             (print "\n"))])

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

(instance (Show String)
  [show (λ [str] {"\"" ++ str ++ "\""})])

(instance (∀ [a] (Show a) => (Show (Maybe a)))
  [show (λ* [[(just x)] {"(just " ++ (show x) ++ ")"}]
            [[nothing ] "nothing"])])

(instance (∀ [a b] (Show a) (Show b) => (Show (Tuple a b)))
  [show (λ [(tuple a b)] {"(tuple " ++ (show a) ++ " " ++ (show b) ++ ")"})])

(instance (∀ [a] (Show a) => (Show (List a)))
  [show (λ* [[{y :: ys}] {"{" ++ (show y) ++ " :: " ++ (show ys) ++ "}"}]
            [[nil      ] "nil"])])

;; ---------------------------------------------------------------------------------------------------
;; Eq

(class (Eq a)
  [== : {a -> a -> Bool}])

(instance (Eq Unit)
  [== (λ [unit unit] true)])

(instance (Eq Bool)
  [== (λ* [[true  y] y]
          [[false y] (not y)])])

(instance (Eq Integer)
  [== equal?/Integer])

(instance (Eq String)
  [== equal?/String])

(instance (∀ [a] (Eq a) => (Eq (Maybe a)))
  [== (λ* [[(just a) (just b)] (== a b)]
          [[nothing  nothing ] true]
          [[_        _       ] false])])

(instance (∀ [a b] (Eq a) (Eq b) => (Eq (Tuple a b)))
  [== (λ [(tuple a b) (tuple c d)] (and (== a c) (== b d)))])
