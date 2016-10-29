#lang racket/base

(require (for-syntax racket/base
                     racket/provide-transform
                     racket/require-transform
                     syntax/id-table)
         racket/splicing
         (rename-in rascal/private/base [class define-class])
         syntax/parse/define)

(provide class rename)

(begin-for-syntax
  (define (make-renaming-transformer id-stx)
    (syntax-parser
      [{~or id:id (id:id . args)}
       #`(splicing-let-syntax ([id (make-rename-transformer (quote-syntax #,id-stx))])
           #,this-syntax)])))

(begin-for-syntax
  (struct class-transformer ()
    #:property prop:procedure
    (let ([transformer (make-renaming-transformer #'define-class)])
      (λ (_ stx) (transformer stx)))
    #:property prop:provide-transformer
    (λ (_)
      (λ (stx modes)
        (syntax-parse stx
          [(_ class-id:local-value/class)
           #:do [(define class (attribute class-id.local-value))]
           #:with [method-id ...] (free-id-table-keys (class-method-table class))
           (expand-export #'(combine-out class-id method-id ...) modes)]))))

  (struct rename-in/out ()
    #:property prop:require-transformer
    (λ (_)
      (syntax-parser
        [(_ {~describe "a module path" mod-path} [out-id:id in-id:id] ...)
         (expand-import #'(rename-in mod-path [out-id in-id] ...))]))
    #:property prop:provide-transformer
    (λ (_)
      (λ (stx modes)
        (syntax-parse stx
          [(_ [in-id:id out-id:id] ...)
           (expand-export #'(rename-out [in-id out-id] ...) modes)])))))

(define-syntax class (class-transformer))
(define-syntax rename (rename-in/out))
