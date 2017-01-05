#lang racket/base

(require hackett/private/kernel)

(provide (all-from-out hackett/private/kernel))

;; ---------------------------------------------------------------------------------------------------
;; module reader

(module reader syntax/module-reader hackett/base
  #:wrapper1 with-hackett-reader-parameterization
  (require hackett/private/reader))
