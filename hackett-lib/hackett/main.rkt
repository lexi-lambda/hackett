#lang racket/base

(require syntax/parse/define

         hackett/prelude
         (only-in hackett/private/adt case* case λ λ* lambda lambda* defn _)
         (only-in hackett/private/class instance)
         (except-in hackett/private/kernel λ lambda)
         hackett/private/provide
         (only-in hackett/private/toplevel @%top-interaction))
(provide (all-from-out hackett/prelude)
         (all-from-out hackett/private/adt)
         (all-from-out hackett/private/class)
         (all-from-out hackett/private/kernel)
         (all-from-out hackett/private/provide)

         (rename-out [@%top-interaction #%top-interaction]))

(module reader syntax/module-reader hackett/main
  #:wrapper1 call-with-hackett-reading-parameterization
  (require hackett/private/reader))
