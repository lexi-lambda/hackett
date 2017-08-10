#lang info

(define collection 'multi)

(define deps
  '("base"
    "hackett-lib"
    ["scribble-lib" #:version "1.16"]))
(define build-deps
  '("racket-doc"
    "sandbox-lib"))
