#lang curly-fn racket/base

(require racket/function
         rackunit
         rackunit/spec
         syntax/parse)

(define (get-type stx)
  (syntax-parse (expand-syntax #`(module m rascal #,stx))
    #:context 'typecheck
    #:literals [module #%plain-module-begin #%plain-app #%plain-lambda]
    [(module _ _
       (#%plain-module-begin
        _ (#%plain-app _ (#%plain-lambda () expr) _)))
     (syntax-property #'expr ':-string)]))

(check-regexp-match
 #px"^\\(→ (g\\d+) \\1\\)$"
 (get-type #'(let ([id (λ (x) x)])
               (let ([const (λ (y z) z)])
                 (const id)))))

(check-regexp-match
 #px"^\\(→ (g\\d+) \\1\\)$"
 (get-type #'(let ([id (λ (x) x)]
                   [const (λ (y z) z)])
               (const id))))

(check-equal? (get-type #'(let ([const (λ (y z) z)])
                            (const 1 "hello")))
              "String")

(check-equal? (get-type #'(let ([id (λ (x) x)])
                            ((id id) 4)))
              "Integer")

(check-equal? (get-type #'(let ([add1 (λ (x) (+ x 1))]
                                [add1-indirection (λ (x) (add1 x))]
                                [add1* add1-indirection])
                            add1*))
              "(→ Integer Integer)")

(check-exn
 #px"could not unify Integer with \\(→ \\(→ Integer \\(→ Integer Integer\\)\\) g\\d+\\)"
 (thunk (expand-syntax #'(module m rascal
                           (let ([always-int (λ (x) 0)]
                                 [foo (λ (x) (always-int x))])
                             (foo 1 +))))))

(describe ":"
  (it "annotates expressions with types"
    (check-equal? (get-type #'(: 3 Integer)) "Integer")
    (check-equal? (get-type #'(: "hello" String)) "String"))

  (it "causes a type error if the annotation does not typecheck"
    (check-exn
     #px"could not unify Integer with String"
     (thunk (get-type #'(: "hello" Integer))))))
