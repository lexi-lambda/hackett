#lang racket/base

(require racket/require)

(require (multi-in rascal/private [kernel prim]))

(provide (all-from-out rascal/private/kernel)
         + - *)

;; ---------------------------------------------------------------------------------------------------
;; module reader

(module reader syntax/module-reader rascal/base)
