#lang rascal/private/kernel

(provide (data Bool) not or and)

(data Bool true false)

(def not : {Bool -> Bool}
  (λ (x) (case x [true false]
                 [false true])))

; TODO: make or/and short-circuiting?
(def or : {Bool -> {Bool -> Bool}}
  (λ (x y) (case x [true  true]
                   [false y])))

(def and : {Bool -> {Bool -> Bool}}
  (λ (x y) (case x [true  y]
                   [false false])))
