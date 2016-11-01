#lang racket/base

(require rascal/private/kernel)

(provide (all-from-out rascal/private/kernel))

;; ---------------------------------------------------------------------------------------------------
;; module reader

(module reader syntax/module-reader rascal/base
  #:wrapper1 with-rascal-reader-parameterization
  (require rascal/private/reader))
