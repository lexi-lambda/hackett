#lang racket/base

(require racket/require)

(require (except-in (multi-in rascal/private [adt base prim]) class)
         rascal/private/provide)

(provide require provide rename only-in all-from-out all-defined-out
         : def λ let letrec data case _ class instance
         ∀ ⇒ → ← Integer String
         + - *
         (rename-out [λ lambda]
                     [⇒ =>]
                     [∀ forall]
                     [→ ->]
                     [← <-]
                     [hash-percent-app #%app]
                     [hash-percent-datum #%datum]
                     [hash-percent-module-begin #%module-begin]))

(module+ internal
  (provide (for-syntax solve-constraints τ~ → τvar τvar-id)
           define-base-type))

;; ---------------------------------------------------------------------------------------------------
;; module reader

(module reader syntax/module-reader rascal)
