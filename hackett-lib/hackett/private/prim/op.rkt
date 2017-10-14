#lang racket/base

(require hackett/private/util/require
         (postfix-in - (combine-in racket/base
                                   racket/flonum
                                   racket/match
                                   racket/promise
                                   racket/string))
         (except-in hackett/private/base)
         hackett/private/prim/type
         hackett/private/prim/type-provide)

;; ---------------------------------------------------------------------------------------------------

(provide (typed-out
          [+ : {Integer -> Integer -> Integer} #:fixity 6 left]
          [- : {Integer -> Integer -> Integer} #:fixity 6 left]
          [* : {Integer -> Integer -> Integer} #:fixity 7 left]
          [quotient! : {Integer -> Integer -> Integer} #:fixity 7 left]
          [remainder! : {Integer -> Integer -> Integer} #:fixity 7 left]
          [show/Integer : {Integer -> String}]
          [equal?/Integer : {Integer -> Integer -> Bool} #:fixity 4 left]
          ;; TODO: haskell has a special infix for comparison operators
          ;;       that disallows mixing them. support this?
          [< : {Integer -> Integer -> Bool} #:fixity 4 left]
          [> : {Integer -> Integer -> Bool} #:fixity 4 left]
          [<= : {Integer -> Integer -> Bool} #:fixity 4 left]
          [>= : {Integer -> Integer -> Bool} #:fixity 4 left]
          [d+ : {Double -> Double -> Double} #:fixity 6 left]
          [d- : {Double -> Double -> Double} #:fixity 6 left]
          [d* : {Double -> Double -> Double} #:fixity 7 left]
          [d/ : {Double -> Double -> Double} #:fixity 7 left]
          [show/Double : {Double -> String}]
          [equal?/Double : {Double -> Double -> Bool}]
          [d< : {Double -> Double -> Bool} #:fixity 4 left]
          [d> : {Double -> Double -> Bool} #:fixity 4 left]
          [d<= : {Double -> Double -> Bool} #:fixity 4 left]
          [d>= : {Double -> Double -> Bool} #:fixity 4 left]
          [integer->double : {Integer -> Double}]
          [equal?/String : {String -> String -> Bool}]
          [append/String : {String -> String -> String}]
          [string-length : {String -> Integer}]
          [string-split : {String -> String -> (List String)}]
          [seq : (∀ a (∀ b b)) #:fixity 0 right]
          [print : {String -> (IO Unit)}]
          [error! : (∀ a {String -> a})]))

(define (boolean->Bool x)
  (if- x true false))

(define list->List
  (match-lambda-
    [(cons x xs) ((:: x) (list->List xs))]
    ['()         nil]))

;; ---------------------------------------------------------------------------------------------------
;; Integer

(define ((+ x) y) (+- (force- x) (force- y)))
(define ((- x) y) (-- (force- x) (force- y)))
(define ((* x) y) (*- (force- x) (force- y)))

(define ((quotient! x) y) (quotient- (force- x) (force- y)))
(define ((remainder! x) y) (remainder- (force- x) (force- y)))

(define (show/Integer a) (format- "~a" (force- a)))
(define ((equal?/Integer a) b) (boolean->Bool (=- (force- a) (force- b))))
(define ((< a) b) (boolean->Bool (<- (force- a) (force- b))))
(define ((> a) b) (boolean->Bool (>- (force- a) (force- b))))
(define ((<= a) b) (boolean->Bool (<=- (force- a) (force- b))))
(define ((>= a) b) (boolean->Bool (>=- (force- a) (force- b))))

;; ---------------------------------------------------------------------------------------------------
;; Double

(define ((d+ x) y) (fl+- (force- x) (force- y)))
(define ((d- x) y) (fl-- (force- x) (force- y)))
(define ((d* x) y) (fl*- (force- x) (force- y)))
(define ((d/ x) y) (fl/- (force- x) (force- y)))

(define (show/Double x) (format "~a" (force- x)))
(define ((equal?/Double x) y) (boolean->Bool (fl=- (force- x) (force- y))))
(define ((d< x) y) (boolean->Bool (fl<- (force- x) (force- y))))
(define ((d> x) y) (boolean->Bool (fl>- (force- x) (force- y))))
(define ((d<= x) y) (boolean->Bool (fl<=- (force- x) (force- y))))
(define ((d>= x) y) (boolean->Bool (fl>=- (force- x) (force- y))))

(define (integer->double x) (real->double-flonum- (force- x)))

;; ---------------------------------------------------------------------------------------------------
;; String

(define ((equal?/String x) y) (boolean->Bool (string=?- (force- x) (force- y))))
(define ((append/String x) y) (string-append- (force- x) (force- y)))
(define (string-length x) (string-length- (force- x)))
(define ((string-split x) y) (list->List (string-split- (force- y) (force- x) #:trim? #f)))

;; ---------------------------------------------------------------------------------------------------

(define ((seq x) y) (force- x) y)

(define (print str)
  (io (λ- (rw)
        (display- (force- str))
        ((tuple rw) unit))))

(define (error! str) (error- (force- str)))
