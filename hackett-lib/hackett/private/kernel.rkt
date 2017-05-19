#lang racket/base

(require (for-syntax racket/base)
         syntax/parse/define

         (rename-in hackett/private/base
                    [@%app @%app1]
                    [∀ ∀1]
                    [=> =>1]))

(provide (rename-out [@%module-begin #%module-begin]
                     [@%top #%top]
                     [@%datum #%datum]
                     [@%app #%app]
                     [@%top-interaction #%top-interaction]
                     [λ lambda]
                     [∀ forall])
         require only-in provide : def λ ∀ -> => Integer String)

(module reader syntax/module-reader hackett/private/kernel)

(define-syntax-parser λ
  [(_ [x:id] e:expr)
   (syntax/loc this-syntax
     (λ1 x e))]
  [(_ [x:id xs:id ...+] e:expr)
   (quasisyntax/loc this-syntax
     (λ1 x #,(syntax/loc this-syntax
               (λ [xs ...] e))))])

(define-syntax-parser ∀
  [(_ [x:id] t)
   (syntax/loc this-syntax
     (∀1 x t))]
  [(_ [x:id xs:id ...+] t)
   (quasisyntax/loc this-syntax
     (∀1 x #,(syntax/loc this-syntax
               (∀ [xs ...] t))))])

(define-syntax-parser =>
  [(_ [x] t)
   (syntax/loc this-syntax
     (=>1 x t))]
  [(_ [x xs ...+] t)
   (quasisyntax/loc this-syntax
     (=>1 x #,(syntax/loc this-syntax
                (=> [xs ...] t))))])

(define-syntax-parser @%app
  [(_ f:expr x:expr)
   (syntax/loc this-syntax
     (@%app1 f x))]
  [(_ f:expr x:expr xs:expr ...+)
   (quasisyntax/loc this-syntax
     (@%app #,(syntax/loc this-syntax
                (@%app1 f x))
            xs ...))])
