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
; a type namespace. In this case, users must explicitly use ‘unmangle-types-in’, possibly with the
; ‘#:only’, ‘#:no-introduce’, or ‘#:prefix’ options in order to flatten the two Hackett namespaces into
; Racket’s single one.

(require (for-syntax racket/base
                     racket/list
                     racket/match
                     racket/provide-transform
                     racket/require-transform
                     threading)
         racket/require
         syntax/parse/define

         (for-syntax hackett/private/typecheck
                     "mangle/mangle-identifier.rkt"
                     "mangle/mangle-reqprov.rkt"))

(provide for-type unmangle-types-in)

(begin-for-syntax
  (define-values [type-id-mangler type-id-unmangler]
    (make-id-mangler #:prefix "#%hackett-type:"
                     #:introducer type-namespace-introduce)))

(define-syntax for-type
  (make-mangling-provide-transformer type-id-mangler))

(define-syntax unmangle-types-in
  (make-unmangling-require-transformer type-id-unmangler))
