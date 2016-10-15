#lang s-exp "lang-unify.rkt"

(let [id (λ x x)]
  (let [const (λ y (λ z z))]
    (const id)))

(let [const (λ y (λ z z))]
  ((const 1) "hello"))

(let [id (λ x x)]
  ((id id) 4))

(let [add1 (λ x ((+ x) 1))]
  (let [add1-indirection (λ x (add1 x))]
    (let [add1* add1-indirection]
      add1*)))

#;(let [always-int (λ x 0)]
  (let [foo (λ x (always-int x))]
    ((foo 1) +)))
