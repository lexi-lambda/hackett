#lang racket/base

(require racket/require
         hackett/private/util/require

         (for-syntax (multi-in racket [base provide-transform]))
         (postfix-in - (combine-in racket/base
                                   racket/match
                                   racket/promise
                                   racket/string))
         syntax/parse/define

         (for-syntax hackett/private/util/stx)
         hackett/data/bool
         hackett/data/list
         hackett/data/tuple
         hackett/data/unit
         (except-in hackett/private/base @%app)
         (only-in hackett/private/kernel [#%app @%app])
         hackett/private/prim/io)

;; ---------------------------------------------------------------------------------------------------

; use the right #%app when type transforming
(define-syntax (#%app stx)
  (syntax-parse stx
    [(_ . more)
     #`(#,(if (type-transforming?) #'@%app #'#%app-)
        . more)]))

(define-syntax typed-out
  (make-provide-pre-transformer
   (λ (stx modes)
     (syntax-parse stx
       #:literals [:]
       [(_ [id:id : t-expr:type] ...)
        #:with [id* ...] (generate-temporaries (attribute id))
        #:with [t ...] (map preservable-property->expression (attribute t-expr.τ))
        #:do [(for-each syntax-local-lift-module-end-declaration
                        (syntax->list
                         #'((define-syntax id* (make-typed-var-transformer #'id t)) ...)))]
        (pre-expand-export #'(rename-out [id* id] ...) modes)]))))

;; ---------------------------------------------------------------------------------------------------

(provide IO main typed-out
         (rename-out [#%app type-#%app])
         (typed-out
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
          [equal?/String : {String -> String -> Bool}]
          [append/String : {String -> String -> String}]
          [string-split : {String -> String -> (List String)}]
          [print : {String -> (IO Unit)}]
          [error! : (∀ a {String -> a})]))

(define (boolean->Bool x)
  (if- x true false))

(define list->List
  (match-lambda-
    [(cons x xs) (:: x (list->List xs))]
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
;; String

(define ((equal?/String x) y) (string=?- (force- x) (force- y)))
(define ((append/String x) y) (string-append- (force- x) (force- y)))
(define ((string-split x) y) (list->List (string-split- (force- y) (force- x))))

;; ---------------------------------------------------------------------------------------------------

(define-syntax-parser main
  [(_ e:expr)
   #'(module+ main
       (void- (with-dictionary-elaboration (force- (@%app unsafe-run-io! e)))))])

(define (print str)
  (io (λ- (rw)
        (display- (force- str))
        ((tuple rw) unit))))

(define (error! str) (error- (force- str)))
