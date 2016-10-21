#lang racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     syntax/transformer)
         racket/lazy-require
         racket/promise
         racket/runtime-path)

(provide lazy-require lazy-require/value)

(begin-for-syntax
  (define-syntax-class lazy-require-clause
    #:attributes [definitions]
    [pattern [module-path [import-id:id ...]]
             #:with runtime-module-path (generate-temporary #'module-path)
             #:with [import-id-promise ...] (generate-temporaries (attribute import-id))
             #:attr definitions
             #'(begin
                 (define-runtime-module-path-index runtime-module-path 'module-path)
                 (begin
                   (define import-id-promise (delay (dynamic-require runtime-module-path 'import-id)))
                   (define-syntax import-id
                     (make-variable-like-transformer #'(force import-id-promise))))
                 ...)]))

(define-syntax lazy-require/value
  (syntax-parser
    [(_ clause:lazy-require-clause ...)
     #'(begin clause.definitions ...)]))
