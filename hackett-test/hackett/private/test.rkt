#lang hackett

(require (only-in racket/base for-syntax module submod))

(module shared hackett
  (provide (data Test-Result))
  (data Test-Result test-success test-failure))

(module untyped racket/base
  (require (for-syntax racket/base)
           racket/promise
           (prefix-in r: rackunit/log)
           syntax/parse/define

           (only-in hackett/private/base submodule-part unmangle-types-in)
           (only-in (unmangle-types-in #:no-introduce hackett)
                    [#%app @%app] : -> IO String Unit unit tuple)
           (only-in hackett/private/prim io unsafe-run-io!)
           hackett/private/prim/type-provide

           (unmangle-types-in #:no-introduce (submod ".." shared)))

  (provide (typed-out [test-log! : {Test-Result -> (IO Unit)}]
                      [println/error : {String -> (IO Unit)}])
           test)

  (define (test-log! result)
    (io (λ (rw)
          (r:test-log! (equal? test-success (force result)))
          ((tuple rw) unit))))

  (define (println/error str)
    (io (λ (rw)
          (displayln (force str) (current-error-port))
          ((tuple rw) unit))))

  (define-syntax-parser test
    [(_ e:expr)
     ; transfer lexical context onto module body to ensure the proper #%module-begin is introduced
     #`(submodule-part test
         #,(datum->syntax this-syntax (syntax-e #'(#%app void (force (@%app unsafe-run-io! e))))))]))

(require (submod "." shared)
         (submod "." untyped))

(provide test ==!)

(defn ==! : (forall [a] (Eq a) (Show a) => {a -> a -> (IO Unit)})
  [[x y] (if {x == y}
             (test-log! test-success)
             (do (println/error
                  {"expectation failed:\n"
                   ++ "  expected: " ++ (show y) ++ "\n"
                   ++ "     given: " ++ (show x)})
                 (test-log! test-failure)))])
