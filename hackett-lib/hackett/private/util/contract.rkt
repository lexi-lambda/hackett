#lang racket/base

(require racket/contract
         racket/set)

(provide (contract-out [immutable-set/c (-> contract? contract?)]))

(define (immutable-set/c elem/c)
  (set/c #:kind 'immutable elem/c))
