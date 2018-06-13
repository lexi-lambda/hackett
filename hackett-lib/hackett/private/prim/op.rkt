#lang racket/base

(require hackett/private/type-reqprov
         hackett/private/util/require

         (postfix-in - (combine-in racket/base
                                   racket/flonum
                                   racket/function
                                   racket/match
                                   racket/promise
                                   racket/string))

         hackett/private/base
         (only-in (unmangle-types-in #:no-introduce (only-types-in hackett/private/kernel)) forall)
         (unmangle-types-in #:no-introduce (only-types-in hackett/private/prim/type))
         (only-in hackett/private/prim/type
                  True False :: Nil Just Nothing
                  [Unit MkUnit] [Tuple MkTuple] [IO MkIO])
         hackett/private/prim/type-provide)

;; ---------------------------------------------------------------------------------------------------

(provide (typed-out
          [+ : {Integer -> Integer -> Integer}]
          [- : {Integer -> Integer -> Integer}]
          [* : {Integer -> Integer -> Integer}]
          [quotient! : {Integer -> Integer -> Integer}]
          [remainder! : {Integer -> Integer -> Integer}]
          [show/Integer : {Integer -> String}]
          [equal?/Integer : {Integer -> Integer -> Bool}]
          [< : {Integer -> Integer -> Bool}]
          [> : {Integer -> Integer -> Bool}]
          [<= : {Integer -> Integer -> Bool}]
          [>= : {Integer -> Integer -> Bool}]
          [d+ : {Double -> Double -> Double}]
          [d- : {Double -> Double -> Double}]
          [d* : {Double -> Double -> Double}]
          [d/ : {Double -> Double -> Double}]
          [show/Double : {Double -> String}]
          [equal?/Double : {Double -> Double -> Bool}]
          [d< : {Double -> Double -> Bool}]
          [d> : {Double -> Double -> Bool}]
          [d<= : {Double -> Double -> Bool}]
          [d>= : {Double -> Double -> Bool}]
          [integer->double : {Integer -> Double}]
          [show/String : {String -> String}]
          [equal?/String : {String -> String -> Bool}]
          [append/String : {String -> String -> String}]
          [string-length : {String -> Integer}]
          [string-split : {String -> String -> (List String)}]
          [string->bytes/utf-8 : {String -> Bytes}]
          [show/Bytes : {Bytes -> String}]
          [equal?/Bytes : {Bytes -> Bytes -> Bool}]
          [append/Bytes : {Bytes -> Bytes -> Bytes}]
          [bytes-length : {Bytes -> Integer}]
          [bytes->string/utf-8 : {Bytes -> (Maybe String)}]
          [seq : (forall [a b] b)]
          [print : {String -> (IO Unit)}]
          [error! : (forall [a] {String -> a})]))

(define (boolean->Bool x)
  (if- x True False))

(define list->List
  (match-lambda-
    [(cons x xs) ((:: x) (list->List xs))]
    ['()         Nil]))

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

(define (show/String x) (format "~v" (force- x)))
(define ((equal?/String x) y) (boolean->Bool (string=?- (force- x) (force- y))))
(define ((append/String x) y) (string-append- (force- x) (force- y)))
(define (string-length x) (string-length- (force- x)))
(define ((string-split x) y) (list->List (string-split- (force- y) (force- x) #:trim? #f)))
(define (string->bytes/utf-8 x) (string->bytes/utf-8- (force- x)))

;; ---------------------------------------------------------------------------------------------------
;; Bytes

(define (show/Bytes x) (format "~v" (force- x)))
(define ((equal?/Bytes x) y) (boolean->Bool (bytes=?- (force- x) (force- y))))
(define ((append/Bytes x) y) (bytes-append- (force- x) (force- y)))
(define (bytes-length x) (bytes-length- (force- x)))
(define (bytes->string/utf-8 x)
  (with-handlers ([exn:fail:contract? (const- Nothing)])
    (Just (bytes->string/utf-8- (force- x)))))

;; ---------------------------------------------------------------------------------------------------

(define ((seq x) y) (force- x) y)

(define (print str)
  (MkIO (λ- (rw)
          (display- (force- str))
          ((MkTuple rw) MkUnit))))

(define (error! str) (error- (force- str)))
