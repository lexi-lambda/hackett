#lang racket/base

(require (for-syntax racket/base
                     racket/syntax
                     version/utils)
         syntax/parse/define)

(provide (for-syntax (all-from-out version/utils))
         cond-expand)

(define-syntax-parser cond-expand
  #:literals [else]
  [(_ {~and clause [{~and {~not else} clause-cond:expr} clause-form ...]} ...
      {~optional [else else-form ...] #:defaults ([[else-form 1] (list #'(begin))])})
   (or (for/or ([clause (in-list (attribute clause))]
                [clause-cond (in-list (attribute clause-cond))]
                [clause-forms (in-list (attribute clause-form))])
         (and (syntax-local-eval clause-cond)
              (quasisyntax/loc clause
                (begin #,@clause-forms))))
       #'(begin else-form ...))])
