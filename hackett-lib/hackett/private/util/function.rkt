#lang racket/base

(provide ~> and~>)

(define (~> x . fs)
  ((apply compose1 (reverse fs)) x))

(define (and~> x . fs)
  (define ((apply-and f) v)
    (and v (f v)))
  ((apply compose1 (map apply-and (reverse fs))) x))
