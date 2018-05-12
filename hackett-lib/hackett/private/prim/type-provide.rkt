#lang racket/base

(require hackett/private/type-reqprov
         hackett/private/util/require
         (for-syntax racket/base
                     racket/provide-transform
                     syntax/parse)
         (postfix-in - racket/base)
         (only-in hackett/private/base define-primop type)
         (only-in hackett/private/kernel :)
         (only-in (unmangle-types-in #:no-introduce (only-types-in hackett/private/kernel))
                  [#%app @%app]))

(provide typed-out)

(define-syntax typed-out
  (make-provide-pre-transformer
   (λ (stx modes)
     (syntax-parse stx
       #:literals [:]
       [(_ [id:id colon:: t] ...)
        ; unhygienically adjust #%app when parsing types to use the type-level #%app
        #:with [#%app-id ...] (for/list ([t (in-list (attribute t))]) (datum->syntax t '#%app))
        #:with [t*:type ...] #'[(let-syntax ([#%app-id (make-rename-transformer #'@%app)]) t) ...]
        #:with [id* ...] (generate-temporaries (attribute id))
        #:do [(for-each syntax-local-lift-module-end-declaration
                        (syntax->list
                         #'((define-primop id* id colon t*.expansion) ...)))]
        (pre-expand-export #'(rename-out [id* id] ...) modes)]))))
