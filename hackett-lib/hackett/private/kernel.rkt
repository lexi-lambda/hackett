#lang curly-fn racket/base

(require (for-syntax hackett/private/infix
                     racket/base
                     syntax/parse/class/paren-shape
                     syntax/parse/experimental/template)
         syntax/parse/define

         (rename-in hackett/private/base
                    [@%app @%app1]
                    [∀ ∀1]
                    [=> =>1]))

(provide (rename-out [@%module-begin #%module-begin]
                     [@%top #%top]
                     [@%datum #%datum]
                     [@%app #%app]
                     [λ lambda]
                     [∀ forall])
         require combine-in except-in only-in prefix-in rename-in
         provide combine-out except-out prefix-out rename-out
         : def λ let letrec ∀ -> => Integer Double String)

(module reader syntax/module-reader hackett/private/kernel
  #:wrapper1 call-with-hackett-reading-parameterization
  (require hackett/private/reader))

(define-syntax-parser λ
  [(_ [x:id] e:expr)
   (syntax/loc this-syntax
     (λ1 x e))]
  [(_ [x:id xs:id ...+] e:expr)
   (quasisyntax/loc this-syntax
     (λ1 x #,(syntax/loc this-syntax
               (λ [xs ...] e))))])

(define-syntax-parser ∀
  #:literals [=>]
  [(_ [x:id] t)
   (syntax/loc this-syntax
     (∀1 x t))]
  [(_ [x:id xs:id ...+] t)
   (quasisyntax/loc this-syntax
     (∀1 x #,(syntax/loc this-syntax
               (∀ [xs ...] t))))]
  [(_ [x:id ...+] constr ... => t)
   (quasisyntax/loc this-syntax
     (∀ [x ...] #,(syntax/loc this-syntax
                    (=> [constr ...] t))))])

(define-syntax-parser =>
  [(_ [x] t)
   (syntax/loc this-syntax
     (=>1 x t))]
  [(_ [x xs ...+] t)
   (quasisyntax/loc this-syntax
     (=>1 x #,(syntax/loc this-syntax
                (=> [xs ...] t))))])

(define-syntax-parser @%app
  [(~parens _ . args)
   (syntax/loc this-syntax
     (@%app/prefix . args))]
  [{~braces _ . args}
   (syntax/loc this-syntax
     (@%app/infix . args))])

(define-syntax-parser @%app/prefix
  [(_ f:expr x:expr)
   (syntax/loc this-syntax
     (@%app1 f x))]
  [(_ f:expr x:expr xs:expr ...+)
   (quasisyntax/loc this-syntax
     (@%app/prefix #,(syntax/loc this-syntax
                       (@%app1 f x))
            xs ...))])

(define-syntax-parser @%app/infix
  [(_ a:expr {~seq op:infix-operator b:expr} ...)
   #:with (_ . op+terms) this-syntax
   (infix->prefix #'op+terms
                  (λ (op a b)
                    (quasisyntax/loc this-syntax
                      (@%app/prefix #,op #,a #,b))))])
