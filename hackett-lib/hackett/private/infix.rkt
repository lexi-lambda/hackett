#lang racket/base

; This module implements support for infix transformer bindings. These allow fixity information to be
; attached to an identifier, which can then be used to parse infix expressions. Currently, only
; associativity is supported, which can be either 'left or 'right. Eventually, it would be good to
; support precedence as well.

(require hackett/private/util/stx
         racket/base
         racket/contract
         syntax/parse
         syntax/parse/class/local-value)

(provide (contract-out
          [prop:infix-operator (struct-type-property/c (-> any/c operator-fixity?))]
          [struct infix-operator-impl ([id identifier?] [fixity operator-fixity?])])
         operator-fixity? infix-operator? infix-operator-fixity infix-operator)

(define operator-fixity?
  (flat-named-contract
   'operator-fixity?
   (or/c 'left 'right)))

(define-values [prop:infix-operator infix-operator? infix-operator-fixity-procedure]
  (make-struct-type-property 'infix-operator))

(define (infix-operator-fixity operator)
  ((infix-operator-fixity-procedure operator) operator))
  
(struct infix-operator-impl (id fixity)
  #:transparent
  #:property prop:procedure
  (λ (operator stx) ((make-variable-like-transformer (infix-operator-impl-id operator)) stx))
  #:property prop:infix-operator
  (λ (operator) (infix-operator-impl-fixity operator)))

(define-syntax-class infix-operator
  #:description #f
  #:commit
  #:attributes [fixity]
  [pattern {~var op (local-value infix-operator?)}
           #:attr fixity (infix-operator-fixity (attribute op.local-value))]
  [pattern _:expr
           #:attr fixity 'left])
