#lang hackett/base

(require (only-in racket/base all-from-out)

         hackett/data/either
         hackett/data/list
         hackett/data/maybe
         hackett/monad/base
         hackett/todo

         (prefix-in prim: hackett/private/prim)
         hackett/private/prim
         hackett/private/provide)

(provide (all-from-out hackett/data/either)
         (all-from-out hackett/data/list)
         (all-from-out hackett/data/maybe)
         (all-from-out hackett/todo)

         (data Unit) (data Bool) (data Tuple) (data Maybe) (data Either) (data List)
         || && not if fst snd

         . $ & id const flip

         (class Eq) (class Show) (class Semigroup) (class Monoid)

         (class Functor) (rename-out [map <$>]) <&> <$ $> ignore
         (class Applicative) sequence traverse
         (class Monad) =<< >>= do ap

         seq error! undefined!
         (for-type IO) main print println
         + - * quotient! remainder! < > <= >=
         d+ d- d* d/ d< d> d<= d>= integer->double
         string-length string-split string->bytes/utf-8
         bytes-length bytes->string/utf-8

         (class Show)
         (class Eq))

;; ---------------------------------------------------------------------------------------------------

(def undefined! : (forall [a] a)
  (error! "undefined!"))

(def print : (forall [m] (Monad-Base IO m) => {String -> (m Unit)})
  {lift/base . prim:print})

(defn println : (forall [m] (Monad-Base IO m) => {String -> (m Unit)})
  [[str] (do (print str)
             (print "\n"))])
