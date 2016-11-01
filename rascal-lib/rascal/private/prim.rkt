#lang racket/base

(require (for-syntax racket/base
                     racket/match
                     racket/provide-transform
                     racket/syntax
                     rascal/private/util/stx)
         (only-in macrotypes/typecheck postfix-in)
         (postfix-in - racket/base)
         rascal/data/bool
         rascal/data/unit
         rascal/private/base
         rascal/private/prim/io
         syntax/parse/define)

;; ---------------------------------------------------------------------------------------------------

(define-syntax typed-out
  (make-provide-pre-transformer
   (λ (stx modes)
     (syntax-parse stx
       #:literals [:]
       [(_ [id:id : τ] ...)
        #:with [id* ...] (generate-temporaries (attribute id))
        #:do [(for-each syntax-local-lift-module-end-declaration
                        (syntax->list
                         #'((define-syntax id*
                              (let ([τ* (type-eval #'τ)])
                                (make-variable-like-transformer/thunk
                                 (λ (stx) (assign-type (syntax/loc stx id)
                                                       (instantiate-type τ*))))))
                            ...)))]
        (pre-expand-export #'(rename-out [id* id] ...) modes)]))))

;; ---------------------------------------------------------------------------------------------------

(provide IO main
         (typed-out
          [+ : (→ Integer (→ Integer Integer))]
          [- : (→ Integer (→ Integer Integer))]
          [* : (→ Integer (→ Integer Integer))]
          [quotient! : (→ Integer (→ Integer Integer))]
          [remainder! : (→ Integer (→ Integer Integer))]
          [equal?/Integer : (→ Integer (→ Integer Bool))]
          [< : (→ Integer (→ Integer Bool))]
          [> : (→ Integer (→ Integer Bool))]
          [<= : (→ Integer (→ Integer Bool))]
          [>= : (→ Integer (→ Integer Bool))]
          [show/Integer : (→ Integer String)]

          [equal?/String : (→ String (→ String Bool))]
          [append/String : (→ String (→ String String))]
          [print! : (→ String (IO Unit))]))

(define (boolean->Bool x)
  (if x true false))

;; ---------------------------------------------------------------------------------------------------
;; Integer

(define ((+ a) b) (+- a b))
(define ((- a) b) (-- a b))
(define ((* a) b) (*- a b))

(define ((quotient! a) b) (quotient- a b))
(define ((remainder! a) b) (remainder- a b))

(define ((equal?/Integer a) b) (boolean->Bool (=- a b)))
(define ((< a) b) (boolean->Bool (<- a b)))
(define ((> a) b) (boolean->Bool (>- a b)))
(define ((<= a) b) (boolean->Bool (<=- a b)))
(define ((>= a) b) (boolean->Bool (>=- a b)))

(define (show/Integer n) (format "~a" n))

;; ---------------------------------------------------------------------------------------------------
;; String

(define ((equal?/String a) b) (boolean->Bool (string=?- a b)))
(define ((append/String a) b) (string-append- a b))

;; ---------------------------------------------------------------------------------------------------
;; IO

(define-syntax-parser main
  [(_ e:expr)
   #:do [(match-define {list _ _ {list e-}}
           (typecheck-annotated-bindings (list (generate-temporary))
                                         (list (type-eval #'(∀ [a] (IO a))))
                                         (list #'e)))]
   #:with e- e-
   #'(module+ main
       (void- (unsafe-run-io! e-)))])

(define (print! str)
  (io (λ- (rw)
        (display- str)
        (tuple2 rw unit))))
