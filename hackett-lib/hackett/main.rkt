#lang racket/base

(require racket/require)

(require (multi-in hackett [base prelude]))

(provide (all-from-out hackett/base)
         (all-from-out hackett/prelude))

;; ---------------------------------------------------------------------------------------------------
;; module reader

(module reader syntax/module-reader hackett
  #:wrapper1 with-hackett-reader-parameterization
  (require hackett/private/reader))
