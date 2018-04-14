#lang racket/base

(require (for-syntax racket/base)
         (for-template racket/base
                       syntax/parse)
         racket/contract
         racket/list
         racket/match
         syntax/parse
         syntax/parse/define
         syntax/parse/experimental/template)

(provide (contract-out [replace-stx-loc (-> syntax? syntax? syntax?)]
                       [make-variable-like-transformer (-> (or/c syntax? (-> identifier? syntax?))
                                                           (-> syntax? syntax?))]
                       [make-pattern-like-pattern-expander (-> (or/c syntax? (-> identifier? syntax?))
                                                                pattern-expander?)]
                       [preservable-property->expression (-> any/c syntax?)]
                       [internal-definition-context-extend
                        (-> (or/c internal-definition-context?
                                  (listof internal-definition-context?)
                                  #f)
                            internal-definition-context?)]
                       [internal-definition-context-cons
                        (-> internal-definition-context?
                            (or/c internal-definition-context?
                                  (listof internal-definition-context?)
                                  #f)
                            (or/c internal-definition-context?
                                  (listof internal-definition-context?)))])
         syntax/loc/props quasisyntax/loc/props template/loc/props quasitemplate/loc/props)

; These two functions are taken with modifications from macrotypes/stx-utils, which implement a
; version of make-variable-like-transformer from syntax/transformer that cooperates better with
; typechecking.
(define (replace-stx-loc old new)
  (let ([old* (syntax-disarm old #f)])
    (syntax-rearm (datum->syntax old* (syntax-e old*) new old) old)))

(define (make-variable-like-transformer ref-stx)
  (syntax-parser
    [_:id
     (replace-stx-loc (if (procedure? ref-stx) (ref-stx this-syntax) ref-stx) this-syntax)]
    [(head:id . args)
     (datum->syntax this-syntax (list* '#%app #'head #'args) this-syntax this-syntax)]))

(define (make-pattern-like-pattern-expander ref-stx)
  (pattern-expander
   (syntax-parser
     [_:id
      (replace-stx-loc (if (procedure? ref-stx) (ref-stx this-syntax) ref-stx) this-syntax)]
     [(head:id . args)
      (syntax/loc this-syntax ({~and head} . args))])))

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

; Like syntax/loc and friends, but copy properties from the source syntax object in addition to source
; location.
(define-syntaxes [syntax/loc/props quasisyntax/loc/props template/loc/props quasitemplate/loc/props]
  (let ()
    (define (make-syntax/loc/props name syntax-id)
      (syntax-parser
        [(_ from-stx-expr:expr {~describe "template" template})
         #`(let ([from-stx from-stx-expr])
             (unless (syntax? from-stx)
               (raise-argument-error '#,name "syntax?" from-stx))
             (let* ([stx (#,syntax-id template)]
                    [stx* (syntax-disarm stx #f)])
               (syntax-rearm (datum->syntax stx* (syntax-e stx*) from-stx from-stx) stx)))]))
    (values (make-syntax/loc/props 'syntax/loc/props #'syntax)
            (make-syntax/loc/props 'quasisyntax/loc/props #'quasisyntax)
            (make-syntax/loc/props 'template/loc/props #'template)
            (make-syntax/loc/props 'quasitemplate/loc/props #'quasitemplate))))

; Creates a new internal definition context that extends a context in the shape local-expand expects.
(define (internal-definition-context-extend old-ctx)
  (if (list? old-ctx)
      (syntax-local-make-definition-context (first old-ctx))
      (syntax-local-make-definition-context old-ctx)))

; Adds to a list of internal definition contexts in the shape that local-expand expects.
(define (internal-definition-context-cons new-ctx old-ctx)
  (cond [(not old-ctx) new-ctx]
        [(list? old-ctx) (cons new-ctx old-ctx)]
        [else (list new-ctx old-ctx)]))
