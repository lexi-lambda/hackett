#lang racket/base

; This module implements support for infix transformer bindings. These allow fixity information to be
; attached to an identifier, which can then be used to parse infix expressions. Currently, only
; associativity is supported, which can be either 'left or 'right. Eventually, it would be good to
; support precedence as well.

(require (for-template racket/base)
         hackett/private/util/stx
         racket/base
         racket/contract
         racket/syntax
         syntax/parse
         syntax/parse/class/local-value)

(provide (contract-out
          [prop:infix-operator (struct-type-property/c (-> any/c (or/c operator-fixity? #f)))]
          [infix-operator-fixity (-> infix-operator? operator-fixity?)]
          [make-infix-variable-like-transformer
           (-> (or/c syntax? (-> syntax? syntax?)) (or/c operator-fixity? #f) (-> syntax? syntax?))]
          [indirect-infix-definition (-> syntax? (or/c operator-fixity? #f) syntax?)])
         operator-fixity? infix-operator? infix-operator fixity-annotation)

(define operator-fixity?
  (flat-named-contract
   'operator-fixity?
   (or/c 'left 'right)))

(define-values [prop:infix-operator has-prop:infix-operator? infix-operator-fixity-procedure]
  (make-struct-type-property 'infix-operator))

(define (infix-operator-fixity operator)
  ((infix-operator-fixity-procedure operator) operator))

(define (infix-operator? x)
  (and (has-prop:infix-operator? x)
       (operator-fixity? (infix-operator-fixity x))))

; Infix transformer bindings; use the make-infix-variable-like-transformer constructor instead of
; creating instances of this struct directly.
(struct infix-variable-like-transformer (procedure fixity)
  #:property prop:procedure (struct-field-index procedure)
  #:property prop:infix-operator
  (λ (operator) (infix-variable-like-transformer-fixity operator)))

(define (make-infix-variable-like-transformer expr fixity)
  (let ([proc (make-variable-like-transformer expr)])
    (if fixity (infix-variable-like-transformer proc fixity) proc)))

(define-syntax-class (infix-operator #:default-fixity [default-fixity 'left])
  #:description #f
  #:commit
  #:attributes [fixity]
  [pattern {~var op (local-value infix-operator?)}
           #:attr fixity (infix-operator-fixity (attribute op.local-value))]
  [pattern _:expr
           #:when default-fixity
           #:attr fixity default-fixity])

(define-splicing-syntax-class fixity-annotation
  #:description "fixity annotation"
  #:attributes [fixity]
  [pattern {~seq #:fixity {~and fixity-datum {~or {~datum left}
                                                  {~datum right}}}}
           #:attr fixity (syntax-e #'fixity-datum)])

; Given a definition and a potential fixity declaration, add a layer of indirection that replaces the
; definition with one that defines an infix operator.
;
; Example:
;
;   > (indirect-infix-definition #'(define :: cons) 'right)
;   #'(begin
;       (define ::1 cons)
;       (define-syntax :: (infix-variable-like-transformer #'::1 'right)))
;
(define (indirect-infix-definition stx fixity)
  (if fixity
      (syntax-parse stx
        #:context 'indirect-infix-definition
        [(d id:id expr)
         #:with id- (generate-temporary #'id)
         #:with fixity-expr (preservable-property->expression fixity)
         #'(begin
             (d id- expr)
             (define-syntax id (make-infix-variable-like-transformer #'id- fixity-expr)))])
      stx))
