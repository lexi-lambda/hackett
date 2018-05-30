#lang racket/base

; Ensure recursive definitions work at the top level.

(require racket/sandbox
         rackunit
         syntax/strip-context)

(define hackett-evaluator (make-evaluator 'hackett))
(define (hackett-eval stx) (hackett-evaluator (strip-context stx)))

(hackett-eval #'(require hackett))
(hackett-eval #'(defn fac : {Integer -> Integer}
                  [[0] 1]
                  [[x] {x * (fac {x - 1})}]))

(check-equal? (hackett-eval #'(fac 6)) (hackett-eval #'720))
