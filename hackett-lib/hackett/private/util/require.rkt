#lang racket/base

(require (for-syntax racket/base)
         racket/require
         racket/require-syntax
         syntax/parse/define)

(provide postfix-in)

(define-for-syntax ((add-postfix postfix) str)
  (string-append str postfix))

(define-require-syntax postfix-in
  (syntax-parser
    [(_ post-id:id require-spec)
     #:with post-str (symbol->string (syntax-e #'post-id))
     #'(filtered-in (add-postfix 'post-str) require-spec)]))
