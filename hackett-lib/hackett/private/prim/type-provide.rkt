#lang racket/base

(require hackett/private/util/require
         (for-syntax hackett/private/util/stx
                     racket/base
                     racket/provide-transform
                     syntax/parse)
         (postfix-in - racket/base)         
         (only-in hackett/private/base define-primop make-typed-var-transformer type type-transforming?)
         (only-in hackett/private/kernel [#%app @%app] :))

(provide #%app typed-out)

; use the right #%app when type transforming
(define-syntax (#%app stx)
  (syntax-parse stx
    [(_ . more)
     #`(#,(if (type-transforming?) #'@%app #'#%app-)
        . more)]))

(define-syntax typed-out
  (make-provide-pre-transformer
   (λ (stx modes)
     (syntax-parse stx
       #:literals [:]
       [(_ [id:id colon:: t:type] ...)
        #:with [id* ...] (generate-temporaries (attribute id))
        #:do [(for-each syntax-local-lift-module-end-declaration
                        (syntax->list
                         #'((define-primop id* id colon t) ...)))]
        (pre-expand-export #'(rename-out [id* id] ...) modes)]))))
