#lang hackett

(require (only-in racket/base module submod))

(module assertions racket/base
  (require (for-syntax racket/base
                       hackett/private/typecheck
                       hackett/private/util/stx)
           rackunit/log
           syntax/macro-testing
           syntax/parse/define
           (only-in hackett/private/typecheck τ->string))

  (provide typecheck-succeed typecheck-fail)

  (define-syntax-parser typecheck!
    [(_ e:expr)
     (parameterize ([current-type-context '()])
       (define-values [e- t] (τ⇒! #'e))
       (preservable-property->expression (apply-current-subst t)))])

  (define-simple-macro (typecheck-succeed e:expr)
    (with-handlers ([exn:fail? (λ (exn)
                                 (test-log! #f)
                                 (eprintf "~a failed to typecheck:\n  ~a\n"
                                          (syntax->datum #'e)
                                          (exn-message exn)))])
      (convert-compile-time-error (typecheck! e))
      (test-log! #t)))

  (define-simple-macro (typecheck-fail e:expr)
    (with-handlers ([exn:fail? (λ (exn) (test-log! #t))])
      (eprintf "~a typechecked successfully, inferred ~a\n"
               (syntax->datum #'e)
               (τ->string (convert-compile-time-error (typecheck! e))))
      (test-log! #f))))

;; ---------------------------------------------------------------------------------------------------

(require (submod "." assertions))

(typecheck-succeed unit)
(typecheck-succeed (: unit Unit))
(typecheck-succeed 1)
(typecheck-succeed (: 1 Integer))
(typecheck-fail (: unit Integer))
(typecheck-fail (: 1 Unit))
(typecheck-fail (unit unit))
(typecheck-fail (1 1))

(typecheck-succeed (λ x x))
(typecheck-succeed (λ x (λ y x)))
(typecheck-succeed ((λ x x) unit))
(typecheck-succeed (: ((λ x x) unit) Unit))
(typecheck-succeed ((λ x x) 1))
(typecheck-succeed (: ((λ x x) 1) Integer))
(typecheck-succeed (((λ x (λ y x)) unit) 1))
(typecheck-succeed (: (((λ x (λ y x)) unit) 1) Unit))
(typecheck-succeed (((λ x (λ y y)) unit) 1))
(typecheck-succeed (: (((λ x (λ y y)) unit) 1) Integer))

(typecheck-fail (: (λ x x) Unit))
(typecheck-fail (: ((λ x x) 1) Unit))
(typecheck-fail (: ((λ x (λ y x)) 1) Unit))
(typecheck-fail (: ((λ x (λ y y)) 1) Unit))

(typecheck-succeed ((tuple unit) unit))
(typecheck-succeed (: ((tuple unit) unit) (Tuple Unit Unit)))
(typecheck-succeed ((tuple 1) 1))
(typecheck-succeed (: ((tuple 1) 1) (Tuple Integer Integer)))
(typecheck-succeed ((tuple 1) unit))
(typecheck-succeed (: ((tuple 1) unit) (Tuple Integer Unit)))
(typecheck-succeed ((tuple unit) 1))
(typecheck-succeed (: ((tuple unit) 1) (Tuple Unit Integer)))

(typecheck-fail (: ((tuple unit) unit) (Tuple Integer Integer)))
(typecheck-fail (: ((tuple unit) unit) (Tuple Unit Integer)))
(typecheck-fail (: ((tuple unit) unit) (Tuple Integer Unit)))

(typecheck-succeed ((tuple-cata (λ x (λ y x))) ((tuple unit) 1)))
(typecheck-succeed (: ((tuple-cata (λ x (λ y x))) ((tuple unit) 1)) Unit))
(typecheck-succeed ((tuple-cata (λ x (λ y y))) ((tuple unit) 1)))
(typecheck-succeed (: ((tuple-cata (λ x (λ y y))) ((tuple unit) 1)) Integer))
(typecheck-succeed (: ((tuple-cata +) ((tuple 1) 1)) Integer))

(typecheck-succeed (: (λ x x) (∀ a (-> a a))))
(typecheck-fail (: (λ x 1) (∀ a (-> a a))))
(typecheck-succeed (: (λ x (λ y x)) (∀ a (∀ b (-> a (-> b a))))))
(typecheck-fail (: (λ x (λ y y)) (∀ a (∀ b (-> a (-> b a))))))
