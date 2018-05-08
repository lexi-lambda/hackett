#lang curly-fn racket/base

(require (for-syntax hackett/private/infix
                     racket/base
                     syntax/parse/class/paren-shape
                     syntax/parse/experimental/template)
         syntax/parse/define

         (rename-in hackett/private/base
                    [@%app @%app1]
                    [#%type:app #%type:app1])
         hackett/private/type-reqprov)

(provide (rename-out [@%module-begin #%module-begin]
                     [@%top #%top]
                     [@%datum #%datum]
                     [@%app #%app]
                     [@%require require]
                     [λ lambda])
         #%require/only-types combine-in except-in only-in prefix-in rename-in
         provide combine-out except-out prefix-out rename-out for-type module+
         : def λ let letrec todo!
         (for-type #:no-introduce ∀ -> => Integer Double String
                   (rename-out [@%top #%top]
                               [#%type:app #%app]
                               [∀ forall])))

(module module-wrapper racket/base
  (require syntax/parse syntax/strip-context)
  (provide module-wrapper-insert-type-require)
  (define (module-wrapper-insert-type-require read-module)
    (syntax-parse (read-module)
      [(module mod-name mod-path
         (#%module-begin form ...))
       (datum->syntax this-syntax
                      (syntax-e (strip-context
                                 #'(module mod-name mod-path
                                     (#%module-begin
                                      (#%require/only-types mod-path)
                                      form ...))))
                      this-syntax
                      this-syntax)])))

(module reader syntax/module-reader hackett/private/kernel
  #:wrapper1 call-with-hackett-reading-parameterization
  #:module-wrapper module-wrapper-insert-type-require
  (require hackett/private/reader
           (submod ".." module-wrapper)))

(define-syntax-parser @%require
  [(_ require-spec ...)
   #'(require (unmangle-types-in require-spec) ...)])

(define-syntax-parser #%require/only-types
  [(_ require-spec ...)
   (type-namespace-introduce
    #'(@%require (only-types-in require-spec ...)))])

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
  [(_ [] t) #'t]
  [(_ [x:id xs:id ...] t)
   (quasisyntax/loc this-syntax
     (#%type:forall x #,(syntax/loc this-syntax
                          (∀ [xs ...] t))))]
  [(_ [x:id ...] constr ... =>/use:=> t)
   (quasisyntax/loc this-syntax
     (∀ [x ...] #,(syntax/loc this-syntax
                    (=>/use [constr ...] t))))])

(define-syntax-parser =>
  [(_ [] t) #'t]
  [(_ [x xs ...] t)
   (quasisyntax/loc this-syntax
     (#%type:qual x #,(syntax/loc this-syntax
                        (=> [xs ...] t))))])

(define-simple-macro (define-infix/currying-#%app @%app @%app1)
  (...
   (begin
     (define-syntax-parser @%app
       [(~parens _ . args)
        (syntax/loc this-syntax
          (@%app/prefix . args))]
       [{~braces _ . args}
        (syntax/loc this-syntax
          (@%app/infix . args))])

     (define-syntax-parser @%app/prefix
       [(_ f:expr) #'f]
       [(_ f:expr x:expr xs:expr ...)
        (quasisyntax/loc this-syntax
          (@%app/prefix #,(syntax/loc this-syntax
                            (@%app1 f x))
                        xs ...))])

     (define-syntax-parser @%app/infix
       [(_ a:expr op:infix-operator b:expr {~seq ops:infix-operator bs:expr} ...+)
        #:when (eq? 'left (attribute op.fixity))
        #:and ~!
        #:fail-unless (andmap #{eq? % 'left} (attribute ops.fixity))
                      "cannot mix left- and right-associative operators in the same infix expression"
        (quasitemplate/loc this-syntax
          (@%app/infix #,(syntax/loc this-syntax
                           (@%app/infix a op b))
                       {?@ ops bs} ...))]
       [(_ {~seq as:expr ops:infix-operator} ...+ a:expr op:infix-operator b:expr)
        #:when (eq? 'right (attribute op.fixity))
        #:and ~!
        #:fail-unless (andmap #{eq? % 'right} (attribute ops.fixity))
                      "cannot mix left- and right-associative operators in the same infix expression"
        (quasitemplate/loc this-syntax
          (@%app/infix {?@ as ops} ...
                       #,(syntax/loc this-syntax
                           (@%app/infix a op b))))]
       [(_ a:expr op:expr b:expr)
        (syntax/loc this-syntax
          (@%app/prefix op a b))]
       [(_ a:expr)
        #'a]))))

(define-infix/currying-#%app @%app @%app1)
(define-infix/currying-#%app #%type:app #%type:app1)
