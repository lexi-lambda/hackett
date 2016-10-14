#lang s-exp "lang-unify.rkt"

(let [id (λ x x)]
  ((id id) 4))
