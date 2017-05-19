#lang racket/base

(provide #%delay-expansion)

(define-syntax-rule (#%delay-expansion form) form)
