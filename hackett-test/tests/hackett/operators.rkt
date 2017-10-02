#lang hackett

(require hackett/private/test)

(test (==! {1 + 2 + 4} 7))
(test (==! {1 * 2 + 3} 5))
(test (==! {3 + 2 * 1} 5))

(def -/r #:fixity 6 right -)

(test (==! {5 - 2 - 1} 2))
(test (==! {5 -/r 2 -/r 1} 4))

(defn suc [[n] {n + 1}])
(defn sqr [[n] {n * n}])

(test (==! {sqr $ 2 + 3} 25))
(test (==! {suc $ sqr $ 2 + 3} 26))
(test (==! {suc $ sqr $ 2 * 3} 37))

(test (==! {3 (λ (x y) x) 4} 3))
(test (==! {3 (λ (x y) y) 4} 4))
(test (==! {3 (λ (x y) (+ x y)) 4 (λ (x y) (* x y)) 5} 35))

(test (==! {1 + 2 :: nil} {3 :: nil}))
