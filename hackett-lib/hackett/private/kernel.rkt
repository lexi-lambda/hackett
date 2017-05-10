#lang racket/base

(require hackett/private/base)

(provide (rename-out [@%module-begin #%module-begin]
                     [@%top #%top]
                     [@%datum #%datum]
                     [@%app #%app]
                     [@%top-interaction #%top-interaction]
                     [λ: λ]
                     [λ: lambda]
                     [∀ forall]
                     [+/curried +])
         require only-in provide : def ∀ -> Unit Integer Tuple
         unit tuple tuple-cata)

(module reader syntax/module-reader hackett/private/kernel)
