#lang racket/base

(require (for-syntax racket/base)
         racket/function
         rackunit
         rackunit/spec
         syntax/parse/define
         syntax/strip-context)

(define (expand-rascal-module-proc stx)
  (parameterize ([current-namespace (make-base-empty-namespace)])
    (namespace-require ''#%kernel)
    (expand (strip-context
             #`(module m rascal
                 (#%module-begin
                  #,@stx))))))

(define-syntax-rule (expand-rascal-module form ...)
  (expand-rascal-module-proc #'(form ...)))

(define-syntax-parser check-typecheck-success
  [(_ form ...)
   #:with this-stx #`(quote-syntax #,this-syntax)
   #:with this-source (datum->syntax #f '() this-syntax)
   #:with src-stx #'(quote-syntax this-source)
   #'(with-check-info*
      (list (make-check-name 'check-typecheck-success)
            (make-check-location (list (syntax-source src-stx)
                                       (syntax-line src-stx)
                                       (syntax-column src-stx)
                                       (syntax-position src-stx)
                                       (syntax-span src-stx)))
            (make-check-expression (syntax->datum this-stx)))
      (thunk (check-not-exn (thunk (expand-rascal-module form ...)))))])

(define-syntax-parser check-typecheck-failure
  [(_ exn-pred form ...)
   #:with this-stx #`(quote-syntax #,this-syntax)
   #:with this-source (datum->syntax #f '() this-syntax)
   #:with src-stx #'(quote-syntax this-source)
   #'(with-check-info*
      (list (make-check-name 'check-typecheck-success)
            (make-check-location (list (syntax-source src-stx)
                                       (syntax-line src-stx)
                                       (syntax-column src-stx)
                                       (syntax-position src-stx)
                                       (syntax-span src-stx)))
            (make-check-expression (syntax->datum this-stx)))
      (thunk (check-exn exn-pred (thunk (expand-rascal-module form ...)))))])

;; ---------------------------------------------------------------------------------------------------

(describe "number literal"
  (it "has the proper type"
    (check-typecheck-success
     (def x : Integer 42))
    (check-typecheck-failure
     #px"could not unify String with Integer"
     (def x : String 3))))

(describe "string literal"
  (it "has the proper type"
    (check-typecheck-success
     (def x : String "hello"))
    (check-typecheck-failure
     #px"could not unify Integer with String"
     (def x : Integer "hello"))))

(describe "ambiguous type"
  (it "is an error"
    (check-typecheck-failure
     #px"type variable ‘([^’]+)’ is ambiguous in \\(Show \\1\\)"
     (def x : String
       (show (right "hello"))))))

(describe "rascal/prelude"
  (describe "List"
    (it "is a polymorphic container"
      (check-typecheck-success
       (require rascal/prelude)
       (def x : (List String)
         (cons "a" (cons "b" nil))))
      (check-typecheck-success
       (require rascal/prelude)
       (def x : (List Integer)
         (cons 1 (cons 2 nil)))))))
