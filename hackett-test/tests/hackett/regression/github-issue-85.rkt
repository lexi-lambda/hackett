#lang hackett

(class (C a)
  [f : {Integer -> a}])

(instance (C Bool)
  [f (λ [n] False)])

(defn g
  [[n] (case (f n)
         [True  "yes"]
         [False "no"])])
