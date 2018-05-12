#lang hackett/private/kernel

(require hackett/private/provide)

(provide (data Unit) (data Bool) (data Tuple) (data Maybe) (data Either) (data List)
         (data IO) (data Real-World))

(data Unit Unit)
(data Bool True False)
(data (Tuple a b) (Tuple a b))
(data (Maybe a) (Just a) Nothing)
(data (Either a b) (Left a) (Right b))
(data (List a)
  {a :: (List a)} #:fixity right
  Nil)

(data Real-World Real-World)
(data (IO a) (IO (-> Real-World (Tuple Real-World a))))
