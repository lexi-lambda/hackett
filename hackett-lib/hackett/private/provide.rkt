#lang racket/base

(require (for-syntax racket/base
                     racket/provide-transform)
         racket/splicing
         syntax/parse/define

         hackett/private/base
         (rename-in hackett/private/adt [data define-data]))

(provide data)

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
           #:with [constructor:data-constructor-spec ...] (τ:con-constructors t)
           (expand-export #'(combine-out type-id constructor.tag ...) modes)])))))

(define-syntax data (data-transformer))
