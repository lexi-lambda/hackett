#lang hackett

(require (only-in racket/base module submod))

(module assertions racket/base
  (require (for-syntax racket/base
                       hackett/private/typecheck
                       hackett/private/util/stx)
           rackunit/log
           syntax/macro-testing
           syntax/parse/define
           (only-in hackett/private/base τ⇒!)
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

(typecheck-succeed 1.0)
(typecheck-succeed (: 1.0 Double))
(typecheck-fail (: 1.0 Integer))
(typecheck-succeed 0.1)
(typecheck-succeed (: 0.1 Double))
(typecheck-fail (: 0.1 Integer))

(typecheck-succeed "hello")
(typecheck-succeed (: "hello" String))
(typecheck-fail (: "hello" Unit))

(typecheck-succeed (λ [x] x))
(typecheck-succeed (λ [x y] x))
(typecheck-succeed ((λ [x] x) unit))
(typecheck-succeed (: ((λ [x] x) unit) Unit))
(typecheck-succeed ((λ [x] x) 1))
(typecheck-succeed (: ((λ [x] x) 1) Integer))
(typecheck-succeed ((λ [x y] x) unit 1))
(typecheck-succeed (: ((λ [x y] x) unit 1) Unit))
(typecheck-succeed ((λ [x y] y) unit 1))
(typecheck-succeed (: ((λ [x y] y) unit 1) Integer))

(typecheck-fail (: (λ [x] x) Unit))
(typecheck-fail (: ((λ [x] x) 1) Unit))
(typecheck-fail (: ((λ [x y] x) 1) Unit))
(typecheck-fail (: ((λ [x y] y) 1) Unit))

(typecheck-succeed (tuple unit unit))
(typecheck-succeed (: (tuple unit unit) (Tuple Unit Unit)))
(typecheck-succeed (tuple 1 1))
(typecheck-succeed (: (tuple 1 1) (Tuple Integer Integer)))
(typecheck-succeed (tuple 1 unit))
(typecheck-succeed (: (tuple 1 unit) (Tuple Integer Unit)))
(typecheck-succeed (tuple unit 1))
(typecheck-succeed (: (tuple unit 1) (Tuple Unit Integer)))

(typecheck-fail (: (tuple unit unit) (Tuple Integer Integer)))
(typecheck-fail (: (tuple unit unit) (Tuple Unit Integer)))
(typecheck-fail (: (tuple unit unit) (Tuple Integer Unit)))

(typecheck-succeed (: (λ [x] x) (∀ [a] {a -> a})))
(typecheck-fail (: (λ [x] 1) (∀ [a] {a -> a})))
(typecheck-succeed (: (λ [x y] x) (∀ [a b] {a -> b -> a})))
(typecheck-fail (: (λ [x y] y) (∀ [a b] {a -> b -> a})))

(typecheck-succeed true)
(typecheck-succeed (: true Bool))
(typecheck-succeed false)
(typecheck-succeed (: false Bool))
(typecheck-fail (: true Unit))
(typecheck-fail (: false Unit))

(typecheck-succeed just)
(typecheck-succeed (: just (∀ [a] {a -> (Maybe a)})))
(typecheck-succeed (: just {Unit -> (Maybe Unit)}))
(typecheck-succeed (just unit))
(typecheck-succeed (: (just unit) (Maybe Unit)))
(typecheck-succeed nothing)
(typecheck-succeed (: nothing (∀ [a] (Maybe a))))
(typecheck-succeed (: nothing (Maybe Unit)))
(typecheck-fail (: just (Maybe Unit)))
(typecheck-fail (: (just unit) (∀ [a] (Maybe a))))
(typecheck-fail (: (just unit) (Maybe Integer)))
(typecheck-fail (: nothing Unit))
(typecheck-fail (: (: nothing (Maybe Unit)) (∀ [a] (Maybe a))))
(typecheck-fail (: (: nothing (Maybe Unit)) (Maybe Integer)))

(typecheck-succeed (case nothing
                     [(just x) x]
                     [nothing unit]))
(typecheck-succeed (: (case nothing
                        [(just x) x]
                        [nothing unit])
                      Unit))
(typecheck-succeed (λ [x] (case x
                            [(just x) x]
                            [nothing unit])))
(typecheck-succeed (: (λ [x] (case x
                               [(just x) x]
                               [nothing unit]))
                      (-> (Maybe Unit) Unit)))
(typecheck-fail (: (λ [x] (case x
                            [(just x) x]
                            [nothing unit]))
                   (-> (Maybe Integer) Unit)))
(typecheck-fail (: (λ [x] (case x
                            [(just x) x]
                            [nothing unit]))
                   (∀ [a] (-> (Maybe a) Unit))))
(typecheck-succeed (case nothing
                     [(just (just x)) x]
                     [_ unit]))
(typecheck-succeed (: (case nothing
                        [(just (just x)) x]
                        [_ unit])
                      Unit))
(typecheck-fail (case nothing
                  [(just x) x]
                  [(just (just x)) x]
                  [_ unit]))
(typecheck-fail (λ [x] (case x
                         [nothing unit]
                         [true unit])))

(typecheck-succeed (λ [m] (case m
                            [nothing nothing]
                            [_ nothing])))
(typecheck-succeed (: (λ [m] (case m
                               [nothing nothing]
                               [_ nothing]))
                      (∀ [a b] {(Maybe a) -> (Maybe b)})))
(typecheck-succeed (λ [f m] (case m
                              [(just x) (just (f x))]
                              [nothing nothing])))
(typecheck-succeed (: (λ [f m] (case m
                                 [(just x) (just (f x))]
                                 [nothing nothing]))
                      (∀ [a b] {{a -> b} -> (Maybe a) -> (Maybe b)})))

(typecheck-succeed {just . (+ 1)})
(typecheck-succeed (: {just . (+ 1)} {Integer -> (Maybe Integer)}))
(typecheck-fail {just . 1})

(typecheck-succeed (let ([x 1]) (+ x 1)))
(typecheck-succeed (: (let ([x 1]) (+ x 1)) Integer))
(typecheck-succeed (let ([x 1] [y x]) (+ x y)))
(typecheck-succeed (: (let ([x 1] [y x]) (+ x y)) Integer))

(typecheck-fail (let ([x "hi"]) (+ x 1)))
(typecheck-fail (let ([x : Integer "hi"]) (+ x 1)))
(typecheck-fail (let ([x : String 1]) {x ++ "!"}))
(typecheck-fail (: (let ([x 1]) (+ x 1)) String))
(typecheck-fail (: (let ([x 1] [y x]) (+ x y)) String))

(typecheck-succeed (letrec ([xs {1 :: xs}]) (take 4 xs)))
(typecheck-succeed (letrec ([xs : (List Integer) {1 :: xs}]) (take 4 xs)))
(typecheck-succeed (: (letrec ([xs {1 :: xs}]) (take 4 xs)) (List Integer)))
(typecheck-succeed (: (letrec ([xs : (List Integer) {1 :: xs}]) (take 4 xs)) (List Integer)))
(typecheck-succeed (letrec ([xs {1 :: ys}] [ys {2 :: xs}]) (take 4 xs)))
(typecheck-succeed (letrec ([xs : (List Integer) {1 :: ys}] [ys {2 :: xs}]) (take 4 xs)))
(typecheck-succeed (: (letrec ([xs {1 :: ys}] [ys {2 :: xs}]) (take 4 xs)) (List Integer)))
(typecheck-succeed (: (letrec ([xs {1 :: ys}] [ys : (List Integer) {2 :: xs}]) (take 4 xs))
                      (List Integer)))

(typecheck-fail (letrec ([xs : Integer {1 :: xs}]) (take 4 xs)))
(typecheck-fail (letrec ([xs 42]) (take 4 xs)))
(typecheck-fail (letrec ([xs {1 :: ys}] [ys 5]) xs))

(typecheck-succeed (λ [xs] (case xs [_ unit])))
(typecheck-succeed (λ [xs] (case xs
                             [nil unit]
                             [{_ :: _} unit])))
(typecheck-fail (λ [xs] (case xs
                          [nil unit])))
(typecheck-succeed (λ [xs] (case xs
                             [nil unit]
                             [{_ :: _ :: _} unit]
                             [{_ :: _} unit])))
(typecheck-fail (λ [xs] (case xs
                          [nil unit]
                          [{_ :: _ :: _} unit])))
(typecheck-fail (λ [xs] (case xs
                          [{_ :: _ :: _} unit]
                          [{_ :: _} unit])))
