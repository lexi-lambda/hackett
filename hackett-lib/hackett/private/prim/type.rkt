#lang hackett/private/kernel

(require (except-in hackett/private/adt data)
         hackett/private/provide)

(provide (data Unit) (data Bool) (data Tuple) (data Maybe) (data Either) (data List)
         (data IO) (data Real-World))

(data Unit unit)
(data Bool true false)
(data (Tuple a b) (tuple a b))
(data (Maybe a) (just a) nothing)
(data (Either a b) (left a) (right b))
(data (List a)
  {a :: (List a)} #:fixity 5 right
  nil)

(data Real-World real-world)
(data (IO a) (io (-> Real-World (Tuple Real-World a))))
