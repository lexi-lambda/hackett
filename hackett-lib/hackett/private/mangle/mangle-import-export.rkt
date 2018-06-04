#lang racket/base

(provide mangle-export
         unmangle-import)

(require racket/match
         racket/provide-transform
         racket/require-transform
         threading
         "mangle-identifier.rkt")

;; ---------------------------------------------------------

;; Export StringMangler -> Export
(define (mangle-export e id-mangler*)
  (match-define (id-mangler intro mangle-str) id-mangler*)
  (struct-copy export e
    [local-id (intro (export-local-id e))]
    [out-sym (~>> (export-out-sym e)
                  symbol->string
                  mangle-str
                  string->symbol)]))

;; Import IdUnmangler -> [Maybe Import]
(define (unmangle-import i id-unmangler)
  (match i
    [(import local-id src-sym src-mod-path mode req-mode orig-mode orig-stx)
     (define unmangled (id-unmangler local-id))
     (and unmangled
          (import unmangled
                  src-sym src-mod-path mode req-mode orig-mode orig-stx))]))

;; ---------------------------------------------------------

