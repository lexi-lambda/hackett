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

           hackett/private/type-reqprov
           (prefix-in t: (unmangle-types-in #:no-introduce (only-types-in hackett)))
           (only-in hackett [#%app @%app] module+ : Unit Tuple)
           (only-in hackett/private/prim IO unsafe-run-io!)
           hackett/private/prim/type-provide

           (unmangle-types-in #:no-introduce (submod ".." shared)))

  (provide (typed-out [test-log! : {Test-Result t:-> (t:IO t:Unit)}]
                      [println/error : {t:String t:-> (t:IO t:Unit)}])
           test)

  (define (test-log! result)
    (IO (λ (rw)
          (r:test-log! (equal? test-success (force result)))
          ((Tuple rw) Unit))))

  (define (println/error str)
    (IO (λ (rw)
          (displayln (force str) (current-error-port))
          ((Tuple rw) Unit))))

  (define-syntax-parser test
    [(_ e:expr)
     ; transfer lexical context to ensure the proper #%module-begin is introduced
     (datum->syntax this-syntax
                    (list #'module+ #'test #'(#%app void (force (@%app unsafe-run-io! e))))
                    this-syntax)]))

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
