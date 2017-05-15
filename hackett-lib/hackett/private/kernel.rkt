#lang racket/base

(require (for-syntax racket/base)
         syntax/parse/define

         hackett/private/base)

(provide (rename-out [@%module-begin #%module-begin]
                     [@%top #%top]
                     [@%datum #%datum]
                     [@%app #%app]
                     [@%top-interaction #%top-interaction]
                     [λ lambda]
                     [∀ forall]
                     [+/curried +])
         require only-in provide : def λ ∀ -> Unit Integer Tuple
         unit tuple tuple-cata)

(module reader syntax/module-reader hackett/private/kernel)

(define-syntax-parser λ
  [(_ [x:id] e:expr)
   #'(λ1 x e)]
  [(_ [x:id xs:id ...+] e:expr)
   #'(λ1 x (λ [xs ...] e))])
