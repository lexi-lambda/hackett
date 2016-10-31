#lang racket/base

(provide with-rascal-reader-parameterization)

(define (with-rascal-reader-parameterization thunk)
  (parameterize ([read-accept-dot #f]
                 [read-accept-infix-dot #f])
    (thunk)))
