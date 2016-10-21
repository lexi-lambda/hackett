#lang curly-fn racket/base

(require racket/require)

(require (for-syntax (multi-in racket [base dict format function list match syntax])
                     (multi-in rascal [private/type util/stx])
                     (multi-in syntax/parse [class/local-value define experimental/specialize])
                     macrotypes/stx-utils
                     syntax/id-table)
         (for-meta 2 racket/base
                     syntax/transformer)
         (only-in macrotypes/typecheck postfix-in type-error)
         (postfix-in - racket/base)
         syntax/parse/define)

(provide (for-syntax (all-defined-out)
                     (all-from-out rascal/private/type))
         (all-defined-out))

;; ---------------------------------------------------------------------------------------------------
;; type constructors

(define-syntax (∀ stx) (raise-syntax-error #f "∀ cannot be used as an expression" stx))

(define-syntax-parser define-base-type
  [(_ τ:id
      {~or {~optional {~seq #:constructors constructors:expr}
                      #:defaults ([constructors #'#f])}
           other-option}
      ...)
   #'(begin
       (define-syntax τ (base-type #'τ constructors))
       (begin-for-syntax
         (define-base-type τ #:constructors constructors other-option ...)))])

(define-base-type → #:arity 2)
(define-base-type Integer)
(define-base-type String)

(begin-for-syntax
  ; a → type constructor that supports multiple arguments
  (define →/curried
    (match-lambda*
      [(list τa τb)
       (→ τa τb)]
      [(list τ τs ..2)
       (→ τ (apply →/curried τs))]))

  ; like →/curried, but interprets (→ τ) as τ
  (define →/curried*
    (match-lambda*
      [(list τ) τ]
      [other (apply →/curried other)]))

  (register-custom-type-printer!
   #'→ (match-lambda
         [(→ τa τb)
          (format "(→ ~a ~a)" (type->string τa) (type->string τb))])))

;; ---------------------------------------------------------------------------------------------------
;; types

(begin-for-syntax
  (define (type-eval stx #:ctx [ctx '()])
    (parameterize ([current-type-var-environment (extend-type-var-environment ctx)])
      (let loop ([stx stx])
        (syntax-parse stx
          #:context 'type-eval
          #:literals [∀]
          [τ:id
           (or (free-id-table-ref (current-type-var-environment) #'τ #f)
               (syntax-local-value #'τ))]
          [(∀ [α:id ...] τ)
           #:do [(define α-types (map fresh (attribute α)))
                 (define α-ids (map τvar-id α-types))
                 (define τ* (type-eval #'τ #:ctx (map cons (attribute α) α-types)))
                 ; call type-free-vars to get the order the type variables appear in τ; this assures
                 ; they will have a canonical order, which allows type=? to work more easily
                 (define α-ids* (filter #{member % α-ids free-identifier=?}
                                        (type-free-vars τ*)))]
           (∀ α-ids* τ*)]
          [(τ a)
           (τapp (loop #'τ)
                 (loop #'a))]
          [(τ a as ...)
           (loop #'((τ a) as ...))]))))

  (define-simple-macro (⊢ e {~literal :} τ)
    (assign-type #`e (type-eval #`τ))))

;; ---------------------------------------------------------------------------------------------------
;; general typed forms

(define-syntax-parser λ1
  [(_ x:id e:expr)
   #:do [(define τv (fresh))
         (define/infer+erase [τ [x-] e-] #'e #:ctx (list (cons #'x τv)))]
   (assign-type #'(λ- (x-) e-)
                (→ τv τ))])

(define-syntax-parser λ
  [(_ (x:id) e:expr)
   #'(λ1 x e)]
  [(_ (x:id xs:id ...) e:expr)
   #'(λ1 x (λ (xs ...) e))])

(define-syntax-parser hash-percent-app1
  [(_ fn arg)
   #:do [(define τv (fresh))
         (define/infer+erase [τ_fn [] fn-] #'fn)
         (define/infer+erase [τ_arg [] arg-] #'arg)]
   (assign-constraint (assign-type (syntax/loc this-syntax
                                     (#%app- fn- arg-))
                                   τv)
                      τ_fn (→ τ_arg τv))])

(define-syntax-parser hash-percent-app
  [(_ fn arg)
   #'(hash-percent-app1 fn arg)]
  [(_ fn arg args ...+)
   #'(hash-percent-app (hash-percent-app fn arg) args ...)])

(define-syntax-parser hash-percent-datum
  [(_ . n:integer)
   (⊢ (#%datum- . n) : Integer)]
  [(_ . n:str)
   (⊢ (#%datum- . n) : String)]
  [(_ . x)
   (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)])

(define-syntax-parser hash-percent-module-begin
  #:literals [#%plain-module-begin-]
  [(_ . body)
   #:with (#%plain-module-begin- . expanded)
          (local-expand #'(#%plain-module-begin- . body)
                        'module-begin null)
   #:do [(define subst (solve-constraints (collect-constraints #'expanded)))]
   #:with substituted (apply-substitutions-to-types subst #'expanded)
   #'(#%module-begin- . substituted)])

(define-syntax-parser let1
  [(_ [x:id val:expr] e:expr)
   #:do [(define/infer+erase [τ_val [] val-] #'val)
         (define subst (solve-constraints (collect-constraints #'val-)))
         (define τ_substituted (apply-subst subst τ_val))
         (define τ_generalized (generalize-type τ_substituted))]
   #:with val-* (assign-type #'val- τ_generalized)
   #:do [(define/infer+erase [τ [x-] e-] #'e #:ctx (list (cons #'x τ_generalized)))]
   (assign-type (syntax/loc this-syntax
                  (let- ([x- val-*]) e-))
                τ)])

(define-syntax-parser let
  [(_ () e:expr)
   #'e]
  [(_ ([x:id val:expr] [xs:id vals:expr] ...) e:expr)
   #'(let1 [x val]
       (let ([xs vals] ...)
         e))])

(define-syntax-parser :
  [(_ e:expr τ-expr)
   #:do [(define τ (type-eval #'τ-expr))
         (define/infer+erase [τ_inferred [] e-] #'e)]
   (assign-constraint (assign-type #'e- τ) τ τ_inferred)])

(define-syntax-parser letrec
  #:literals [:]
  [(_ ([x:id : τ-ann val:expr] ...) body:expr)
   #:do [(define τs_ann (map type-eval (attribute τ-ann)))
         (define/infers+erase [{list* τ_body τs_inferred} [x- ...] [body- val- ...]]
           (cons #'body (attribute val))
           #:ctx (map cons (attribute x) τs_ann))
         (define subst (solve-constraints (collect-constraints #'(val- ...))))
         (match-define {list* τ_body_substituted τs_substituted}
           (map #{apply-subst subst %} (list* τ_body τs_inferred)))
         (define τs_generalized (map generalize-type τs_substituted))
         (define τ_invalid (for/or ([x-id (in-list (attribute x))]
                                    [τ_ann (in-list τs_ann)]
                                    [τ_generalized (in-list τs_generalized)])
                             (and (not (type=? τ_ann τ_generalized))
                                  (list x-id τ_ann τ_generalized))))]
   #:fail-when τ_invalid
               (~a "the inferred type of ‘" (syntax-e (first τ_invalid)) "’ does not match the "
                   "provided type annotation\n"
                   "  annotated: " (type->string (second τ_invalid)) "\n"
                   "  inferred: " (type->string (third τ_invalid)))
   #:with [val-generalized ...] (map assign-type (attribute val-) τs_generalized)
   (assign-constraints (assign-type (syntax/loc this-syntax
                                      (letrec- ([x- val-generalized] ...) body-))
                                    τ_body_substituted)
                       (map cons τs_ann τs_generalized))])

;; ---------------------------------------------------------------------------------------------------
;; primitive operators

(define-simple-macro (define-primop id:id [e:expr {~literal :} τ])
  (define-syntax id (make-variable-like-transformer (⊢ e : τ))))

(define ((+/c a) b) (+- a b))
(define ((-/c a) b) (-- a b))
(define ((*/c a) b) (*- a b))

(define-primop + [+/c : (→ Integer (→ Integer Integer))])
(define-primop - [-/c : (→ Integer (→ Integer Integer))])
(define-primop * [*/c : (→ Integer (→ Integer Integer))])
