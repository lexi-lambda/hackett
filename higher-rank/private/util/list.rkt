#lang curly-fn racket/base

(require racket/contract
         racket/list)

(provide (contract-out [snoc (-> list? any/c list?)]
                       [until (->* [list? any/c] [(-> any/c any/c any/c)] list?)]))

(define (snoc lst x) (append lst (list x)))
(define (until lst x [=? equal?]) (takef lst #{not (=? x %)}))
