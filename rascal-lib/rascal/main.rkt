#lang racket/base

(require racket/require)

(require (multi-in rascal [base prelude]))

(provide (all-from-out rascal/base)
         (all-from-out rascal/prelude))

;; ---------------------------------------------------------------------------------------------------
;; module reader

(module reader syntax/module-reader rascal
  #:wrapper1 with-rascal-reader-parameterization
  (require rascal/private/reader))
