#lang racket/base

(require hackett/private/util/require
         (for-syntax hackett/private/util/stx
                     hackett/private/infix
                     racket/base
                     racket/syntax
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

(begin-for-syntax
  (define-syntax-class typed-out-spec
    #:description "typed-out spec"
    #:attributes [id id* defn]
    [pattern [id:id {~literal :} t:type {~optional :fixity-annotation}]
             #:with id* (generate-temporary #'id)
             #:with defn
             (indirect-infix-definition
              #'(define-primop id* id : t)
              (attribute fixity))]))

(define-syntax typed-out
  (make-provide-pre-transformer
   (λ (stx modes)
     (syntax-parse stx
       [(_ spec:typed-out-spec ...)
        #:do [(for-each syntax-local-lift-module-end-declaration
                        (syntax->list #'(spec.defn ...)))]
        (pre-expand-export #'(rename-out [spec.id* spec.id] ...) modes)]))))
