#lang hackett/private/kernel

(require (except-in hackett/private/adt data)
         hackett/private/provide)

(provide (data Unit) (data Bool) (data Tuple) (data Maybe) (data List)
         (data IO) (data Real-World))

(data Unit unit)
(data Bool true false)
(data (Tuple a b) (tuple a b))
(data (Maybe a) (just a) nothing)
(data (List a)
  {a :: (List a)} #:fixity right
  nil)

(data Real-World real-world)
(data (IO a) (io (-> Real-World (Tuple Real-World a))))
