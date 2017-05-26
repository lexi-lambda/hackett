#lang hackett/private/kernel

(require (only-in racket/base except-in)
         (except-in hackett/private/adt data)
         hackett/private/provide)

(provide (data Bool) not or and if bool)

(data Bool true false)

(defn not : {Bool -> Bool}
  [[true ] false]
  [[false] true])

(defn or : {Bool -> Bool -> Bool}
  [[true  _] true]
  [[false y] y])

(defn and : {Bool -> Bool -> Bool}
  [[true  y] y]
  [[false _] false])

(defn if : (∀ [a] {Bool -> a -> a -> a})
  [[true  x _] x]
  [[false _ y] y])

(defn bool : (∀ [a] {a -> a -> Bool -> a})
  [[x y b] (if b x y)])
