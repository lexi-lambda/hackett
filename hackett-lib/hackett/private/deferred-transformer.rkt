#lang racket/base

(require (for-syntax racket/base
                     racket/contract
                     racket/match
                     racket/syntax

                     hackett/private/expand+elaborate)
         syntax/parse/define

         hackett/private/base)

(provide (for-syntax make-expected-type-transformer))

(define-syntax deferred-expected-type-transformer
  (make-elaborating-transformer
   (syntax-parser
     [(_ expected-type proc orig-stx)
      (match (syntax-local-elaborate-pass)
        [(or 'expand 'elaborate)
         (attach-type (syntax-local-elaborate-defer this-syntax) #'expected-type)]
        ['finalize
         (τ⇐! #'(do-expected-type-transformer proc orig-stx) #'expected-type)])])))

(define-syntax do-expected-type-transformer
  (make-elaborating-transformer
   #:allowed-passes '[finalize]
   (syntax-parser
     [(_ proc orig-stx)
      ((syntax-e #'proc)
       (attach-expected #'orig-stx (apply-current-subst (get-expected this-syntax))))])))

(begin-for-syntax
  (define/contract (make-expected-type-transformer proc)
    (-> (-> syntax? syntax?) (-> syntax? syntax?))
    (make-elaborating-transformer
     (λ (stx) (let ([expected-type #`(#%type:wobbly-var #,(generate-temporary))])
                #`(deferred-expected-type-transformer #,expected-type #,proc #,stx))))))
