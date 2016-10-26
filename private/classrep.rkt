#lang racket/base

(require racket/contract
         syntax/id-table)

(provide (struct-out class)
         (struct-out instance)
         (struct-out ⇒)
         (struct-out has-class))

(struct class (id method-table method-types-quantified-id instances) #:prefab)
(struct instance (dict-id) #:prefab)

(struct ⇒ (context τ) #:prefab)
(struct has-class (class-id τ) #:prefab)
