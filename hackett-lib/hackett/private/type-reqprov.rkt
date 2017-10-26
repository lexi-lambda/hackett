#lang racket/base

; This module implements require and provide transformers for mangling and unmangling type imports and
; exports. This is necessary because Hackett has two namespaces: a type namespace, and a value
; namespace. Within a module, this is easily accommodated by the hygiene system (each namespace has
; its own unique scope), but when it comes to imports and exports, there is a problem. Specifically,
; Racket modules only allow a single binding to be exported per symbol, per phase, so it’s impossible
; to import two different bindings with the same name.
;
; To get around this, exports in the type namespace are mangled by the ‘type-out’ provide transformer,
; then subsequently unmangled by the ‘unmangle-types-in’ require transformer. This mangling scheme
; currently prepends ‘#%hackett-type:’ to the beginning of symbols, but that should be treated
; entirely as an implementation detail, not a part of Hackett’s public interface.
;
; Generally, when writing Hackett code, this is all transparent. Hackett programmers export types
; using ‘type-out’, and Hackett’s ‘require’ implicitly surrounds its subforms with
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
         racket/provide
         racket/require
         syntax/parse/define

         (for-syntax hackett/private/typecheck))

(provide type-out only-types-in unmangle-types-in)

(begin-for-syntax
  (define (mangle-type-name name)
    (string-append "#%hackett-type:" name))

  (define mangled-type-regexp #rx"^#%hackett-type:(.+)$")
  (define (unmangle-type-name name)
    (and~> (regexp-match mangled-type-regexp name) second))
  (define (unmangle-value-name name)
    (and (not (regexp-match? mangled-type-regexp name)) name)))

(define-syntax type-out
  (make-provide-pre-transformer
   (λ (stx modes)
     (syntax-parse stx
       [(_ {~optional {~and #:no-introduce no-introduce?}} provide-spec ...)
        (pre-expand-export
         #`(filtered-out mangle-type-name
                         #,((if (attribute no-introduce?) values type-namespace-introduce)
                            #'(combine-out provide-spec ...)))
         modes)]))))

(define-syntax only-types-in
  (make-require-transformer
   (syntax-parser
     [(_ require-spec ...)
      (expand-import
       #`(filtered-in (λ (name) (and (regexp-match? mangled-type-regexp name) name))
                      (combine-in require-spec ...)))])))

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
