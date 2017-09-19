#lang racket/base

(require hackett/base
         hackett/prelude)
(provide (all-from-out hackett/base)
         (all-from-out hackett/prelude))

(module reader syntax/module-reader hackett/main
  #:wrapper1 call-with-hackett-reading-parameterization
  (require hackett/private/reader))
