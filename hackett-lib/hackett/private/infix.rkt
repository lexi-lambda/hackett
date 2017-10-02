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
          [struct (left-operator-fixity operator-fixity) ([precedence exact-nonnegative-integer?])]
          [struct (right-operator-fixity operator-fixity) ([precedence exact-nonnegative-integer?])]
          [prop:infix-operator (struct-type-property/c (-> any/c operator-fixity?))]
          [struct infix-operator-impl
            ([id identifier?]
             [fixity operator-fixity?])])
         operator-fixity? operator-fixity-precedence
         default-operator-fixity
         default-operator-precedence
         infix-operator? infix-operator-fixity
         infix-operator fixity-annotation indirect-infix-definition
         infix->prefix)

(struct operator-fixity (precedence) #:prefab)
(struct left-operator-fixity operator-fixity () #:prefab)
(struct right-operator-fixity operator-fixity () #:prefab)

(define default-operator-fixity (left-operator-fixity 9))
(define default-operator-precedence (operator-fixity-precedence default-operator-fixity))

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
           #:attr fixity default-operator-fixity])

(define-splicing-syntax-class precedence
  #:description "operator precedence"
  #:attributes [precedence]
  [pattern n:nat #:attr precedence (syntax-e #'n)]
  [pattern {~seq} #:attr precedence default-operator-precedence])

(define-splicing-syntax-class fixity-annotation
  #:description "fixity annotation"
  #:datum-literals [left right]
  #:attributes [fixity]
  [pattern {~seq #:fixity p:precedence left}
           #:attr fixity (left-operator-fixity (attribute p.precedence))]
  [pattern {~seq #:fixity p:precedence right}
           #:attr fixity (right-operator-fixity (attribute p.precedence))])

; Given a definition and a potential fixity declaration, add a layer of indirection that replaces the
; definition with one that defines an infix operator.
;
; Example:
;
;   > (indirect-infix-definition #'(define :: cons) (right-operator-fixity 6))
;   #'(begin
;       (define ::1 cons)
;       (define-syntax :: (infix-operator-impl #'::1 (right-operator-fixity 6))))
;
(define/contract (indirect-infix-definition stx fixity)
  (-> syntax? (or/c operator-fixity? #f) syntax?)
  (if fixity
      (syntax-parse stx
        #:context 'indirect-infix-definition
        [(d id:id . defn-parts)
         #:with id- (generate-temporary #'id)
         #:with fixity-expr (preservable-property->expression fixity)
         #'(begin
             (d id- . defn-parts)
             (define-syntax id (infix-operator-impl #'id- fixity-expr)))])
      stx))


; Converts brace-enclosed infix syntax to prefix notation, using
; the function 'join-fn' to convert an operator and two arguments into
; an expression that applies the operator.
(define/contract (infix->prefix stx join-fn)
  (-> syntax? (-> identifier? syntax? syntax? syntax?) syntax?)

  (define (op->fixity o)
    (define v (syntax-local-value o))
    (if (infix-operator? v)
        (infix-operator-fixity v)
        default-operator-fixity))

  (define (climb stx min-prec)
    (syntax-parse stx
      [(a op . term+ops)
       #:do [(define fixity (op->fixity #'op))
             (define op-prec (operator-fixity-precedence fixity))
             (define greater-prec
               (if (right-operator-fixity? fixity)
                   (sub1 op-prec)
                   op-prec))]
       #:when (> op-prec min-prec)
       #:with (b . op+terms) (climb #'term+ops greater-prec)
       #:with a+b (join-fn #'op #'a #'b)
       (climb (syntax/loc stx
                (a+b . op+terms))
              min-prec)]

      [_ stx]))

  (car (syntax-e (climb stx -1))))
