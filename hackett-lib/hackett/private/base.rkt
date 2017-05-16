#lang curly-fn racket/base

(require racket/require hackett/private/util/require)

(require (for-syntax (multi-in racket [base list match syntax])
                     threading)
         (postfix-in - racket/base)
         (multi-in racket [match splicing])
         syntax/parse/define

         (for-syntax hackett/private/typecheck
                     hackett/private/util/list
                     hackett/private/util/stx))

(provide (for-syntax (all-from-out hackett/private/typecheck))
         #%module-begin #%top
         (rename-out [#%module-begin @%module-begin]
                     [#%top @%top]
                     [∀ forall])
         @%datum @%app @%top-interaction
         define-primop define-base-type
         -> ∀ Integer String
         : λ1 def)

(define-simple-macro (define-base-type name:id)
  (define-syntax name (make-type-variable-transformer (τ:con #'name #f))))

(define-base-type Integer)
(define-base-type String)

(define-syntax-parser define-primop
  [(_ op:id op-:id t-expr:type)
   #:with t (preservable-property->expression (attribute t-expr.τ))
   #'(define-syntax op (make-typed-var-transformer #'op- t))])

(define-syntax -> (make-type-variable-transformer τ:->))
(define-syntax-parser ∀
  #:literals [let-values]
  [(∀ x:id t)
   #:with x- (generate-temporary #'x)
   #:with x/τ (preservable-property->expression (τ:var #'x-))
   #:with (let-values _ (let-values _ t-:type))
          (local-expand #'(let-syntax ([x (make-variable-like-transformer
                                           (syntax-property #'(void) 'τ x/τ))])
                            t)
                        'expression '())
   (τ-stx-token (τ:∀ #'x- (attribute t-.τ)))])

(define-syntax-parser @%datum
  [(_ . n:integer)
   (attach-type #'(#%datum . n) (parse-type #'Integer))]
  [(_ . s:str)
   (attach-type #'(#%datum . s) (parse-type #'String))]
  [(_ . x)
   (raise-syntax-error #f "literal not supported" #'x)])

(define-syntax-parser :
  [(_ e t-expr:type)
   (attach-type (τ⇐! #'e (attribute t-expr.τ)) (apply-current-subst (attribute t-expr.τ)))])

(define-syntax-parser λ1
  [(_ x:id e:expr)
   #:do [(define t (get-expected this-syntax))]
   #:fail-unless t "no expected type, add more type annotations"
   #:fail-unless (τ:->? t) (format "expected ~a, given function" (τ->string t))
   #:do [(match-define (τ:->* a b) t)
         (modify-type-context #{snoc % (ctx:assump #'x a)})
         (define-values [xs- e-] (τ⇐/λ! #'e b (list (cons #'x a))))
         (modify-type-context #{ctx-remove % (ctx:assump #'x a)})]
   #:with [x-] xs-
   (attach-type #`(λ- (x-) #,e-) t)]
  [(_ x:id e:expr)
   #:do [(define x^ (generate-temporary))
         (define y^ (generate-temporary))
         (modify-type-context #{append % (list (ctx:var^ x^) (ctx:var^ y^) (ctx:assump #'x (τ:var^ x^)))})
         (define-values [xs- e-] (τ⇐/λ! #'e (τ:var^ y^) (list (cons #'x (τ:var^ x^)))))
         (modify-type-context #{ctx-remove % (ctx:assump #'x (τ:var^ x^))})]
   #:with [x-] xs-
   (attach-type #`(λ- (x-) #,e-) (τ:->* (τ:var^ x^) (τ:var^ y^)))])

(define-syntax (@%app stx)
  (if (type-transforming?)
      (syntax-parse stx
        [(_ a:type b:type)
         (τ-stx-token (τ:app (attribute a.τ) (attribute b.τ)))])
      (syntax-parse stx
        [(_ f:expr e:expr)
         #:do [(define-values [f- t_f] (τ⇒! #'f))
               (define-values [e- t_r] (τ⇒app! (apply-current-subst t_f) #'e))]
         (attach-type #`(#%app #,f- #,e-) t_r)])))

(define-syntax-parser def
  #:literals [:]
  [(_ id:id : t:type e:expr)
   #:with id- (generate-temporary #'id)
   #:with t-expr (preservable-property->expression (attribute t.τ))
   #'(begin-
       (define- id- (: e t))
       (define-syntax- id
         (make-typed-var-transformer #'id- t-expr)))]
  [(_ id:id e:expr)
   #:do [(define-values [e-stx- t]
           (parameterize ([current-type-context '()])
             (let-values ([(e-stx- t) (τ⇒! #'e)])
               (values e-stx- (apply-current-subst t)))))]
   #:with id- (generate-temporary #'id)
   #:with e- e-stx-
   #:with t-expr (preservable-property->expression (generalize t))
   #'(begin-
       (define- id- e-)
       (define-syntax- id
         (make-typed-var-transformer #'id- t-expr)))])

(define-syntax-parser :infer/print-type
  [(_ e)
   (parameterize ([current-type-context '()])
     (~> (τ⇒! #'e)
         (λ () _)
         (call-with-values _ list)
         second
         apply-current-subst
         τ->string
         displayln))
   #'(void)])

(define-syntax-parser @%top-interaction
  [(_ . e)
   (parameterize ([current-type-context '()])
     (define-values [e- τ_e] (τ⇒! #'e))
     (printf ": ~a\n" (τ->string (apply-current-subst τ_e)))
     e-)])

;; ---------------------------------------------------------------------------------------------------

(define ((+/curried- x) y) (+ x y))

; TODO: move this into a place that has access to hackett/private/kernel’s @%app so it can use the
; currying shorthand and is generally less awful
(splicing-let-syntax ([#%app (make-rename-transformer #'@%app)])
  (define-primop +/curried +/curried- ((-> Integer) ((-> Integer) Integer))))
