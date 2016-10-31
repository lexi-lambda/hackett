#lang racket/base

(require racket/require)

(require (except-in (multi-in rascal/private [adt base]) class data)
         rascal/private/provide)

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

(module reader syntax/module-reader rascal/private/kernel
  #:wrapper1 with-rascal-reader-parameterization
  (require rascal/private/reader))
