#lang racket/base

(require racket/require)

(require (multi-in rascal/private [adt base]))

(provide : λ let letrec data case _ class instance ⇒
         ∀ → Integer String
         + - * show/Integer string-append
         (rename-out [hash-percent-app #%app]
                     [hash-percent-datum #%datum]
                     [hash-percent-module-begin #%module-begin]))

(module+ internal
  (provide (for-syntax solve-constraints τ~ → τvar τvar-id)
           define-base-type))

;; ---------------------------------------------------------------------------------------------------
;; module reader

(module reader syntax/module-reader rascal)
