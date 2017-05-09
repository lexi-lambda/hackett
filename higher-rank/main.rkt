#lang curly-fn racket/base

(module reader syntax/module-reader higher-rank)

(require (for-syntax racket/base
                     racket/list
                     racket/match
                     racket/syntax
                     threading)
         racket/match
         syntax/parse/define

         (for-syntax higher-rank/private/typecheck
                     higher-rank/private/util/list
                     higher-rank/private/util/stx))

(provide #%module-begin #%top
         (rename-out [datum #%datum]
                     [app #%app]
                     [top-interaction #%top-interaction]
                     [λ: λ]
                     [λ: lambda]
                     [∀ forall]
                     [+/curried +])
         Unit -> ∀ Tuple Integer
         : unit tuple tuple-cata app)

(define unit- (let () (struct unit ()) (unit)))
(define-syntax unit (make-typed-var-transformer #'unit- τ:unit))

(define-syntax-parser define-primop
  [(_ op:id op-:id t-expr:type)
   #:with t (preservable-property->expression (attribute t-expr.τ))
   #'(define-syntax op (make-typed-var-transformer #'op- t))])

(define-syntax-parser Unit
  [_:id (τ-stx-token τ:unit)])
(define-syntax-parser ->
  [(-> a:type b:type) (τ-stx-token (τ:->* (attribute a.τ) (attribute b.τ)))])
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

(define-for-syntax τ:tuple (τ:con #'Tuple))
(define-syntax-parser Tuple
  [(_ a:type b:type)
   (τ-stx-token (τ:app (τ:app τ:tuple (attribute a.τ)) (attribute b.τ)))])

(define-for-syntax τ:integer (τ:con #'Integer))
(define-syntax-parser Integer
  [_:id (τ-stx-token τ:integer)])

(define ((tuple- x) y) `#s(tuple ,x ,y))
(define-primop tuple tuple- (∀ a (∀ b (-> a (-> b (Tuple a b))))))

(define ((tuple-cata- f) t)
  (match-let ([`#s(tuple ,x ,y) t])
    ((f x) y)))
(define-primop tuple-cata tuple-cata- (∀ a (∀ b (∀ c (-> (-> a (-> b c)) (-> (Tuple a b) c))))))

(define ((+/curried- x) y) (+ x y))
(define-primop +/curried +/curried- (-> Integer (-> Integer Integer)))

(define-syntax-parser datum
  [(_ . n:integer)
   (attach-type #'(#%datum . n) τ:integer)])

(define-syntax-parser :
  [(_ e t-expr:type)
   #:do [(define t (attribute t-expr.τ))
         (define-values [e- t⇒] (τ⇒! (attach-expected #'e t)))]
   #:fail-when (and (not (τ=? t t⇒)) #'e) (format "type mismatch: expected ~a, produced ~a"
                                                  (τ->string t) (τ->string t⇒))
   e-])

(define-syntax-parser λ:
  [(_ x:id e:expr)
   #:do [(define t (get-expected this-syntax))]
   #:fail-unless t "no expected type, add more type annotations"
   #:fail-unless (τ:->? t) (format "expected ~a, given function" (τ->string t))
   #:do [(match-define (τ:->* a b) t)
         (modify-type-context #{snoc % (ctx:assump #'x a)})
         (define-values [xs- e-] (τ⇐/λ! #'e b (list (cons #'x a))))
         (modify-type-context #{ctx-until % (ctx:assump #'x a)})]
   #:with [x-] xs-
   (attach-type #`(λ (x-) #,e-) t)]
  [(_ x:id e:expr)
   #:do [(define x^ (generate-temporary))
         (define y^ (generate-temporary))
         (modify-type-context #{append % (list (ctx:var^ x^) (ctx:var^ y^) (ctx:assump #'x (τ:var^ x^)))})
         (define-values [xs- e-] (τ⇐/λ! #'e (τ:var^ y^) (list (cons #'x (τ:var^ x^)))))
         (modify-type-context #{ctx-until % (ctx:assump #'x (τ:var^ x^))})]
   #:with [x-] xs-
   (attach-type #`(λ (x-) #,e-) (τ:->* (τ:var^ x^) (τ:var^ y^)))])

(define-syntax-parser app
  [(_ f:expr e:expr)
   #:do [(define-values [f- t_f] (τ⇒! #'f))
         (define-values [e- t_r] (τ⇒app! (apply-current-subst t_f) #'e))]
   (attach-type #`(#%app #,f- #,e-) t_r)])

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

(define-syntax-parser top-interaction
  [(_ . e)
   (parameterize ([current-type-context '()])
     (define-values [e- τ_e] (τ⇒! #'e))
     (printf ": ~a\n" (τ->string (apply-current-subst τ_e)))
     e-)])
