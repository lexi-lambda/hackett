#lang racket/base

(require racket/require
         hackett/private/util/require

         (for-syntax (multi-in racket [base provide-transform]))
         (postfix-in - racket/base)
         syntax/parse/define

         (for-syntax hackett/private/util/stx)
         hackett/data/bool
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

(provide IO main
         (typed-out
          [+ : {Integer -> Integer -> Integer}]
          [- : {Integer -> Integer -> Integer}]
          [* : {Integer -> Integer -> Integer}]
          [quotient! : {Integer -> Integer -> Integer}]
          [remainder! : {Integer -> Integer -> Integer}]
          [equal?/Integer : {Integer -> Integer -> Bool}]
          [< : {Integer -> Integer -> Bool}]
          [> : {Integer -> Integer -> Bool}]
          [<= : {Integer -> Integer -> Bool}]
          [>= : {Integer -> Integer -> Bool}]
          [append/String : {String -> String -> String}]
          [print : {String -> (IO Unit)}]))

(define (boolean->Bool x)
  (if x true false))

;; ---------------------------------------------------------------------------------------------------
;; Integer

(define ((+ x) y) (+- x y))
(define ((- x) y) (-- x y))
(define ((* x) y) (*- x y))

(define ((quotient! x) y) (quotient- x y))
(define ((remainder! x) y) (remainder- x y))

(define ((equal?/Integer a) b) (boolean->Bool (=- a b)))
(define ((< a) b) (boolean->Bool (<- a b)))
(define ((> a) b) (boolean->Bool (>- a b)))
(define ((<= a) b) (boolean->Bool (<=- a b)))
(define ((>= a) b) (boolean->Bool (>=- a b)))

;; ---------------------------------------------------------------------------------------------------
;; String

(define ((append/String x) y) (string-append- x y))

;; ---------------------------------------------------------------------------------------------------

(define-syntax-parser main
  [(_ e:expr)
   #'(module+ main
       (void- (with-dictionary-elaboration (@%app unsafe-run-io! e))))])

(define (print str)
  (io (λ- (rw)
        (display- str)
        ((tuple rw) unit))))
