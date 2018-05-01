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
           (only-in hackett/private/typecheck type->string))

  (provide typecheck-succeed typecheck-fail)

  (define-syntax-parser typecheck!
    [(_ e:expr)
     (parameterize ([current-type-context '()])
       (define-values [e- t] (τ⇒! #'e))
       #`(quote-syntax #,(apply-current-subst t)))])

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
               (type->string (convert-compile-time-error (typecheck! e))))
      (test-log! #f))))

;; ---------------------------------------------------------------------------------------------------

(require (submod "." assertions))

(typecheck-succeed Unit)
(typecheck-succeed (: Unit Unit))
(typecheck-succeed 1)
(typecheck-succeed (: 1 Integer))
(typecheck-fail (: Unit Integer))
(typecheck-fail (: 1 Unit))
(typecheck-fail (Unit Unit))
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
(typecheck-succeed ((λ [x] x) Unit))
(typecheck-succeed (: ((λ [x] x) Unit) Unit))
(typecheck-succeed ((λ [x] x) 1))
(typecheck-succeed (: ((λ [x] x) 1) Integer))
(typecheck-succeed ((λ [x y] x) Unit 1))
(typecheck-succeed (: ((λ [x y] x) Unit 1) Unit))
(typecheck-succeed ((λ [x y] y) Unit 1))
(typecheck-succeed (: ((λ [x y] y) Unit 1) Integer))

(typecheck-fail (: (λ [x] x) Unit))
(typecheck-fail (: ((λ [x] x) 1) Unit))
(typecheck-fail (: ((λ [x y] x) 1) Unit))
(typecheck-fail (: ((λ [x y] y) 1) Unit))

(typecheck-succeed (Tuple Unit Unit))
(typecheck-succeed (: (Tuple Unit Unit) (Tuple Unit Unit)))
(typecheck-succeed (Tuple 1 1))
(typecheck-succeed (: (Tuple 1 1) (Tuple Integer Integer)))
(typecheck-succeed (Tuple 1 Unit))
(typecheck-succeed (: (Tuple 1 Unit) (Tuple Integer Unit)))
(typecheck-succeed (Tuple Unit 1))
(typecheck-succeed (: (Tuple Unit 1) (Tuple Unit Integer)))

(typecheck-fail (: (Tuple Unit Unit) (Tuple Integer Integer)))
(typecheck-fail (: (Tuple Unit Unit) (Tuple Unit Integer)))
(typecheck-fail (: (Tuple Unit Unit) (Tuple Integer Unit)))

(typecheck-succeed (: (λ [x] x) (forall [a] {a -> a})))
(typecheck-fail (: (λ [x] 1) (forall [a] {a -> a})))
(typecheck-succeed (: (λ [x y] x) (forall [a b] {a -> b -> a})))
(typecheck-fail (: (λ [x y] y) (forall [a b] {a -> b -> a})))

(typecheck-succeed True)
(typecheck-succeed (: True Bool))
(typecheck-succeed False)
(typecheck-succeed (: False Bool))
(typecheck-fail (: True Unit))
(typecheck-fail (: False Unit))

(typecheck-succeed Just)
(typecheck-succeed (: Just (forall [a] {a -> (Maybe a)})))
(typecheck-succeed (: Just {Unit -> (Maybe Unit)}))
(typecheck-succeed (Just Unit))
(typecheck-succeed (: (Just Unit) (Maybe Unit)))
(typecheck-succeed Nothing)
(typecheck-succeed (: Nothing (forall [a] (Maybe a))))
(typecheck-succeed (: Nothing (Maybe Unit)))
(typecheck-fail (: Just (Maybe Unit)))
(typecheck-fail (: (Just Unit) (forall [a] (Maybe a))))
(typecheck-fail (: (Just Unit) (Maybe Integer)))
(typecheck-fail (: Nothing Unit))
(typecheck-fail (: (: Nothing (Maybe Unit)) (forall [a] (Maybe a))))
(typecheck-fail (: (: Nothing (Maybe Unit)) (Maybe Integer)))

(typecheck-succeed (case Nothing
                     [(Just x) x]
                     [Nothing Unit]))
(typecheck-succeed (: (case Nothing
                        [(Just x) x]
                        [Nothing Unit])
                      Unit))
(typecheck-succeed (λ [x] (case x
                            [(Just x) x]
                            [Nothing Unit])))
(typecheck-succeed (: (λ [x] (case x
                               [(Just x) x]
                               [Nothing Unit]))
                      (-> (Maybe Unit) Unit)))
(typecheck-fail (: (λ [x] (case x
                            [(Just x) x]
                            [Nothing Unit]))
                   (-> (Maybe Integer) Unit)))
(typecheck-fail (: (λ [x] (case x
                            [(Just x) x]
                            [Nothing Unit]))
                   (forall [a] (-> (Maybe a) Unit))))
(typecheck-succeed (case Nothing
                     [(Just (Just x)) x]
                     [_ Unit]))
(typecheck-succeed (: (case Nothing
                        [(Just (Just x)) x]
                        [_ Unit])
                      Unit))
(typecheck-fail (case Nothing
                  [(Just x) x]
                  [(Just (Just x)) x]
                  [_ Unit]))
(typecheck-fail (λ [x] (case x
                         [Nothing Unit]
                         [True Unit])))

(typecheck-succeed (λ [m] (case m
                            [Nothing Nothing]
                            [_ Nothing])))
(typecheck-succeed (: (λ [m] (case m
                               [Nothing Nothing]
                               [_ Nothing]))
                      (forall [a b] {(Maybe a) -> (Maybe b)})))
(typecheck-succeed (λ [f m] (case m
                              [(Just x) (Just (f x))]
                              [Nothing Nothing])))
(typecheck-succeed (: (λ [f m] (case m
                                 [(Just x) (Just (f x))]
                                 [Nothing Nothing]))
                      (forall [a b] {{a -> b} -> (Maybe a) -> (Maybe b)})))

(typecheck-succeed {Just . (+ 1)})
(typecheck-succeed (: {Just . (+ 1)} {Integer -> (Maybe Integer)}))
(typecheck-fail {Just . 1})

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

(typecheck-succeed (λ [xs] (case xs [_ Unit])))
(typecheck-succeed (λ [xs] (case xs
                             [Nil Unit]
                             [{_ :: _} Unit])))
(typecheck-fail (λ [xs] (case xs
                          [Nil Unit])))
(typecheck-succeed (λ [xs] (case xs
                             [Nil Unit]
                             [{_ :: _ :: _} Unit]
                             [{_ :: _} Unit])))
(typecheck-fail (λ [xs] (case xs
                          [Nil Unit]
                          [{_ :: _ :: _} Unit])))
(typecheck-fail (λ [xs] (case xs
                          [{_ :: _ :: _} Unit]
                          [{_ :: _} Unit])))
