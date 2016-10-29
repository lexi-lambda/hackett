#lang racket/base

(require (for-syntax racket/base
                     racket/provide-transform
                     rascal/util/stx
                     syntax/parse)
         (only-in macrotypes/typecheck postfix-in)
         (postfix-in - racket/base)
         rascal/data/unit
         rascal/private/base
         rascal/private/prim/io)

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

(provide IO
         (typed-out
          [+ : (→ Integer (→ Integer Integer))]
          [- : (→ Integer (→ Integer Integer))]
          [* : (→ Integer (→ Integer Integer))]
          [show/Integer : (→ Integer String)]
          [append/String : (→ String (→ String String))]
          [display : (→ String (IO Unit))]))

;; ---------------------------------------------------------------------------------------------------
;; Integer

(define ((+ a) b) (+- a b))
(define ((- a) b) (-- a b))
(define ((* a) b) (*- a b))

(define (show/Integer n) (format "~a" n))

;; ---------------------------------------------------------------------------------------------------
;; String

(define ((append/String a) b) (string-append- a b))

;; ---------------------------------------------------------------------------------------------------
;; IO

(define (display str)
  (io (λ- (rw)
        (display- str)
        (tuple2 rw unit))))
