#lang racket/base

(provide with-hackett-reader-parameterization)

(define (with-hackett-reader-parameterization thunk)
  (parameterize ([read-accept-dot #f]
                 [read-accept-infix-dot #f])
    (thunk)))
