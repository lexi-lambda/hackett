#lang racket/base

(require (for-syntax racket/base
                     racket/list
                     racket/syntax
                     syntax/transformer)
         racket/match
         syntax/parse/define)

(provide (struct-out ∀)
         (struct-out τ~)
         (struct-out base-type)
         (struct-out τvar)
         (struct-out τapp)
         define-base-type)

(struct ∀ (τvars τ) #:prefab)
(struct τ~ (a b src) #:prefab)
(struct base-type (id constructors) #:prefab)
(struct τvar (id) #:prefab)
(struct τapp (τ arg) #:prefab)

(define-simple-macro (define-base-type τ:id
                       {~or {~optional {~seq #:arity arity:nat}
                                       #:defaults ([arity #'0])}
                            {~optional {~seq #:constructors constructors:expr}
                                       #:defaults ([constructors #'#f])}}
                       ...)
  #:with τ-value (generate-temporary #'τ)
  #:with [τ_arg ...] (generate-temporaries (make-list (syntax-e #'arity) #f))
  #:do [(define (make-nested-τapps base-stx)
          (let loop ([acc base-stx]
                     [vars (attribute τ_arg)])
            (if (empty? vars) acc
                (loop #`(τapp #,acc #,(first vars))
                      (rest vars)))))]
  #:with nested-τapps-pat (make-nested-τapps #'(base-type (? (λ (id) (free-identifier=? #'τ id))) _))
  #:with nested-τapps-constructor (make-nested-τapps #'(base-type #'τ constructors))
  #:with value-definition
         (if (zero? (syntax-e (attribute arity)))
             #'(define τ-value nested-τapps-constructor)
             #'(define (τ-value τ_arg ...)
                 nested-τapps-constructor))
  (begin
    value-definition
    (define-match-expander τ
      (syntax-parser
        [(_ {~var τ_arg id} ...)
         #'nested-τapps-pat])
      (make-variable-like-transformer #'τ-value))))
