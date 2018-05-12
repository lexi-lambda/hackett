#lang curly-fn racket/base

; This module implements require and provide transformers for mangling and unmangling type imports and
; exports. This is necessary because Hackett has two namespaces: a type namespace, and a value
; namespace. Within a module, this is easily accommodated by the hygiene system (each namespace has
; its own unique scope), but when it comes to imports and exports, there is a problem. Specifically,
; Racket modules only allow a single binding to be exported per symbol, per phase, so it’s impossible
; to import two different bindings with the same name.
;
; To get around this, exports in the type namespace are mangled by the ‘for-type’ provide transformer,
; then subsequently unmangled by the ‘unmangle-types-in’ require transformer. This mangling scheme
; currently prepends ‘#%hackett-type:’ to the beginning of symbols, but that should be treated
; entirely as an implementation detail, not a part of Hackett’s public interface.
;
; Generally, when writing Hackett code, this is all transparent. Hackett programmers export types
; using ‘for-type’, and Hackett’s ‘require’ implicitly surrounds its subforms with
; ‘unmangle-types-in’, so types are automatically injected into the proper namespace. This gets a bit
; trickier, however, when interoperating with Racket modules, which obviously do not have a notion of
; a type namespace. In this case, users must explicitly use ‘only-types-in’ or ‘unmangle-types-in’
; with the ‘#:no-introduce’ or ‘#:prefix’ options in order to flatten the two Hackett namespaces into
; Racket’s single one.

(require (for-syntax racket/base
                     racket/list
                     racket/match
                     racket/provide-transform
                     racket/require-transform
                     threading)
         racket/require
         syntax/parse/define

         (for-syntax hackett/private/typecheck))

(provide for-type only-types-in unmangle-types-in)

(begin-for-syntax
  (define mangled-type-regexp #rx"^#%hackett-type:(.+)$")
  (define (unmangle-type-name name)
    (and~> (regexp-match mangled-type-regexp name) second))

  (struct for-type-transformer ()
    #:property prop:require-transformer
    (λ (self)
      (syntax-parser
        [(_ require-spec ...)
         #:do [(define-values [imports sources] (expand-import (syntax/loc this-syntax
                                                                 (combine-in require-spec ...))))]
         (values (for/list ([i (in-list imports)])
                   (struct-copy import i [local-id (type-namespace-introduce (import-local-id i))]))
                 sources)]))
    #:property prop:provide-transformer
    (λ (self)
      (λ (stx modes)
        (syntax-parse stx
          [(_ {~optional {~and #:no-introduce no-introduce?}} provide-spec ...)
           (for/list ([e (in-list (expand-export (syntax/loc this-syntax
                                                   (combine-out provide-spec ...))
                                                 modes))])
             (struct-copy export e
                          [local-id (if (attribute no-introduce?)
                                        (export-local-id e)
                                        (type-namespace-introduce (export-local-id e)))]
                          [out-sym (~>> (export-out-sym e)
                                        symbol->string
                                        (string-append "#%hackett-type:")
                                        string->symbol)]))])))))

(define-syntax for-type (for-type-transformer))

(define-syntax only-types-in
  (make-require-transformer
   (syntax-parser
     [(_ require-spec ...)
      (expand-import
       #`(matching-identifiers-in #,mangled-type-regexp (combine-in require-spec ...)))])))

(define-syntax unmangle-types-in
  (make-require-transformer
   (syntax-parser
     [(_ {~or {~optional {~or {~and #:no-introduce no-introduce?}
                              {~seq #:prefix prefix:id}}}}
         require-spec ...)
      #:do [(define-values [imports sources] (expand-import #'(combine-in require-spec ...)))]
      (values (map (match-lambda
                     [(and i (import local-id src-sym src-mod-path mode req-mode orig-mode orig-stx))
                      (let* ([local-name (symbol->string (syntax-e local-id))]
                             [unmangled-type-name (unmangle-type-name local-name)])
                        (if unmangled-type-name
                            (let* ([prefixed-type-name
                                    (if (attribute prefix)
                                        (string-append (symbol->string (syntax-e #'prefix))
                                                       unmangled-type-name)
                                        unmangled-type-name)]
                                   [unmangled-id (datum->syntax local-id
                                                                (string->symbol prefixed-type-name)
                                                                local-id
                                                                local-id)])
                              (import (if (or (attribute no-introduce?)
                                              (attribute prefix))
                                          unmangled-id
                                          (type-namespace-introduce unmangled-id))
                                      src-sym src-mod-path mode req-mode orig-mode orig-stx))
                            i))])
                   imports)
              sources)])))
