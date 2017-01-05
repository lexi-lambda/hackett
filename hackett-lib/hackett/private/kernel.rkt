#lang racket/base

(require racket/require)

(require (except-in (multi-in hackett/private [adt base]) class data)
         hackett/private/provide)

(provide require provide rename only-in all-from-out all-defined-out
         : def λ let letrec data case _ class instance
         ∀ ⇒ → ← Integer String
         (rename-out [λ lambda]
                     [⇒ =>]
                     [∀ forall]
                     [→ ->]
                     [← <-]
                     [hash-percent-app #%app]
                     [hash-percent-datum #%datum]
                     [hash-percent-module-begin #%module-begin]))

;; ---------------------------------------------------------------------------------------------------
;; module reader

(module reader syntax/module-reader hackett/private/kernel
  #:wrapper1 with-hackett-reader-parameterization
  (require hackett/private/reader))
