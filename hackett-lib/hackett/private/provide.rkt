#lang racket/base

(require (for-syntax racket/base
                     racket/provide-transform
                     syntax/id-table)
         racket/splicing
         syntax/parse/define

         hackett/private/base
         (rename-in hackett/private/class [class define-class])
         (rename-in hackett/private/adt [data define-data]))

(provide data class)

(begin-for-syntax
  (define (make-renaming-transformer id-stx)
    (syntax-parser
      [_:id id-stx]
      [(_:id . args) (quasisyntax/loc this-syntax (#,id-stx . args))])))

(begin-for-syntax
  (struct data-transformer ()
    #:property prop:procedure
    (let ([transformer (make-renaming-transformer #'define-data)])
      (λ (_ stx) (transformer stx)))
    #:property prop:provide-pre-transformer
    (λ (s)
      (λ (stx modes)
        (syntax-parse stx
          [(data type-id:id)
           (quasisyntax/loc this-syntax
             (data #,(pre-expand-export #'(type-out type-id) modes)
                   #,(type-namespace-introduce #'type-id)))])))
    #:property prop:provide-transformer
    (λ (s)
      (λ (stx modes)
        (syntax-parse stx
          [(_ type-out-spec {~and _:id type-id:type})
           #:do [(define t (attribute type-id.τ))]
           #:fail-when (and (not (τ:con? t)) #'type-id)
                       "not defined as a datatype"
           #:fail-when (and (not (τ:con-constructors t)) #'type-id)
                       "type does not have visible constructors"
           #:with [ctor-tag ...] (τ:con-constructors t)
           (expand-export #'(combine-out type-out-spec ctor-tag ...) modes)]))))

  (struct class-transformer ()
    #:property prop:procedure
    (let ([transformer (make-renaming-transformer #'define-class)])
      (λ (_ stx) (transformer stx)))
    #:property prop:provide-pre-transformer
    (λ (s)
      (λ (stx modes)
        (syntax-parse stx
          [(class class-id:id)
           (quasisyntax/loc this-syntax
             (class #,(pre-expand-export #'(type-out class-id) modes)
                    #,(type-namespace-introduce #'class-id)))])))
    #:property prop:provide-transformer
    (λ (_)
      (λ (stx modes)
        (syntax-parse stx
          [(_ type-out-spec class-id:class-id)
           #:do [(define class (attribute class-id.local-value))]
           #:with [method-id ...] (free-id-table-keys (class:info-method-table class))
           (expand-export #'(combine-out type-out-spec method-id ...) modes)])))))

(define-syntax data (data-transformer))
(define-syntax class (class-transformer))
