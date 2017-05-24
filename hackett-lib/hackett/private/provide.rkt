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
      [{~or id:id (id:id . args)}
       #`(splicing-let-syntax ([id (make-rename-transformer (quote-syntax #,id-stx))])
           #,this-syntax)])))

(begin-for-syntax
  (struct data-transformer ()
    #:property prop:procedure
    (let ([transformer (make-renaming-transformer #'define-data)])
      (λ (_ stx) (transformer stx)))
    #:property prop:provide-transformer
    (λ (s)
      (λ (stx modes)
        (syntax-parse stx
          [(_ {~and _:id type-id:type})
           #:do [(define t (attribute type-id.τ))]
           #:fail-when (and (not (τ:con? t)) #'type-id)
                       "not defined as a datatype"
           #:fail-when (and (not (τ:con-constructors t)) #'type-id)
                       "type does not have visible constructors"
           #:with [[constructor:data-constructor-spec] ...] (τ:con-constructors t)
           (expand-export #'(combine-out type-id constructor.tag ...) modes)]))))

  (struct class-transformer ()
    #:property prop:procedure
    (let ([transformer (make-renaming-transformer #'define-class)])
      (λ (_ stx) (transformer stx)))
    #:property prop:provide-transformer
    (λ (_)
      (λ (stx modes)
        (syntax-parse stx
          [(_ class-id:class-id)
           #:do [(define class (attribute class-id.local-value))]
           #:with [method-id ...] (free-id-table-keys (class:info-method-table class))
           (expand-export #'(combine-out class-id method-id ...) modes)])))))

(define-syntax data (data-transformer))
(define-syntax class (class-transformer))
