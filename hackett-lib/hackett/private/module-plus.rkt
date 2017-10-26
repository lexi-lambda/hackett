#lang curly-fn racket/base

; This module contains an alternative implementation of ‘module+’ from racket/base that avoids
; ‘syntax-local-lift-module-end-declaration’, which does not interact well with Hackett’s namespacing
; system (since declarations are lifted outside the scope of the syntax parameterization that controls
; which scope introducers are currently in effect).
;
; This implementation simply provides a form, ‘with-module+-lift-target’, that can be used in
; Hackett’s ‘#%module-begin’ to essentially capture lifted module declarations.

(require (for-syntax racket/base
                     racket/list)
         racket/splicing
         racket/stxparam
         syntax/parse/define)

(provide module+ with-module+-lift-target)

(define-syntax-parameter current-lifted-submodule-parts #f)

(begin-for-syntax
  (define (lift-submodule-part! submod-name stx)
    (hash-update! (syntax-parameter-value #'current-lifted-submodule-parts)
                  submod-name #{cons (syntax-local-introduce stx) %} '()))

  (define (submodule-parts->submodules all-parts)
    (for/list ([(name parts) (in-hash all-parts)])
      (let ([parts* (map syntax-local-introduce (reverse parts))])
        (datum->syntax (first parts*)
                       (list* #'module* name #f parts*)
                       (first parts*))))))

(define-simple-macro (module+ name:id body ...)
  #:fail-unless (eq? (syntax-local-context) 'module) "not at module top level"
  #:fail-unless (syntax-parameter-value #'current-lifted-submodule-parts)
                "not in a context that allows partial module declarations"
  #:do [(lift-submodule-part!
         (syntax-e #'name)
         (datum->syntax this-syntax
                        (cons #'begin (attribute body))
                        this-syntax))]
  (begin))

(define-simple-macro (with-module+-lift-target form ...)
  (splicing-syntax-parameterize ([current-lifted-submodule-parts (make-hasheq)])
    form ...
    (lifted-submodules)))

(define-simple-macro (lifted-submodules)
  #:with [submod-decl ...] (submodule-parts->submodules
                            (syntax-parameter-value #'current-lifted-submodule-parts))
  (begin submod-decl ...))
