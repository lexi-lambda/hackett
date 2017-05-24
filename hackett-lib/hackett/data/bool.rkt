#lang hackett/private/kernel

(require (only-in racket/base except-in)
         (except-in hackett/private/adt data)
         hackett/private/provide)

(provide (data Bool) not or and if bool)

(data Bool true false)

(def not : {Bool -> Bool}
  (λ [x] (case x [true false]
                 [false true])))

(def or : {Bool -> Bool -> Bool}
  (λ [x y] (case x [true true]
                   [false y])))

(def and : {Bool -> Bool -> Bool}
  (λ [x y] (case x [true y]
                   [false false])))

(def if : (∀ [a] {Bool -> a -> a -> a})
  (λ [b x y] (case b [true x]
                     [false y])))

(def bool : (∀ [a] {a -> a -> Bool -> a})
  (λ [x y b] (if b x y)))
