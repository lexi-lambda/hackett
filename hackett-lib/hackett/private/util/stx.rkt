#lang racket/base

(require racket/contract
         racket/match)

(provide (contract-out [make-variable-like-transformer (-> syntax? any)]
                       [preservable-property->expression (-> any/c syntax?)]))

; These two functions are taken from macrotypes/stx-utils, which implement a version of
; make-variable-like-transformer from syntax/transformer that cooperates better with typechecking.
(define (replace-stx-loc old new)
  (datum->syntax (syntax-disarm old #f) (syntax-e (syntax-disarm old #f)) new old))
(define (make-variable-like-transformer ref-stx)
  (unless (syntax? ref-stx)
    (raise-type-error 'make-variable-like-transformer "syntax?" ref-stx))
  (lambda (stx)
    (syntax-case stx ()
      [id
       (identifier? #'id)
       (replace-stx-loc ref-stx stx)]
      [(id . args)
       (let ([stx* (list* '#%app #'id (cdr (syntax-e stx)))])
         (datum->syntax stx stx* stx stx))])))

; Sometimes, it is useful to embed a value in a piece of syntax. Normally, this is easily achievable
; using quasisyntax/unsyntax, but in the case of embedding prefab structs, the macroexpander will
; mess with their contents. Specifically, if a prefab struct contains a syntax object, then the prefab
; struct is embedded in a piece of syntax, the macroexpander will “flatten” it such that the syntax
; information is lost.
;
; A hacky way around this is to convert values to expressions that evaluate to themselves, then embed
; those into the resulting syntax instead of the values directly.
(define preservable-property->expression
  (match-lambda
    [(and (app prefab-struct-key (? values prefab-key))
          (app struct->vector (vector _ fields ...)))
     #`(make-prefab-struct '#,prefab-key #,@(map preservable-property->expression fields))]
    [(? list? lst)
     #`(list #,@(map preservable-property->expression lst))]
    [(cons a b)
     #`(cons #,(preservable-property->expression a)
             #,(preservable-property->expression b))]
    [(? syntax? stx)
     #`(quote-syntax #,stx)]
    [(and (or (? boolean?) (? symbol?) (? number?) (? char?) (? string?) (? bytes?) (? regexp?))
          datum)
     #`(quote #,datum)]
    [other
     (error 'preservable-property->expression
            "disallowed value within preserved syntax property\n  value: ~e"
            other)]))
