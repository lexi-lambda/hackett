#lang curly-fn racket/base

(provide λ let +
         (rename-out [hash-percent-app #%app]
                     [hash-percent-datum #%datum]
                     [hash-percent-module-begin #%module-begin]))

(require (for-syntax macrotypes/stx-utils
                     racket/base
                     racket/hash
                     racket/list
                     racket/match
                     racket/syntax
                     syntax/id-table
                     syntax/parse/define
                     "util/stx.rkt")
         (for-meta 2 racket/base
                     racket/syntax
                     syntax/transformer)
         (only-in macrotypes/typecheck
                  postfix-in type-error
                  get-stx-prop/car)
         (postfix-in - racket/base)
         (prefix-in kernel: '#%kernel)
         syntax/parse/define)

;; ---------------------------------------------------------------------------------------------------
;; type constructors

(begin-for-syntax
  (struct ∀ (τvars τ) #:prefab)
  (struct τ~ (a b src) #:prefab)
  (struct base-type (id) #:prefab)
  (struct τvar (id) #:prefab)
  (struct τapp (τ arg) #:prefab))

(define-syntax (∀ stx) (raise-syntax-error #f "∀ cannot be used as an expression" stx))

(define-simple-macro (define-base-type τ:id {~optional {~seq #:arity arity:nat}
                                                       #:defaults ([arity #'0])})
  #:with τ-proc (generate-temporary #'τ)
  #:with [τ_arg ...] (generate-temporaries (make-list (syntax-e #'arity) #f))
  #:do [(define (make-nested-τapps base-stx)
          (let loop ([acc base-stx]
                     [vars (attribute τ_arg)])
            (if (empty? vars) acc
                (loop #`(τapp #,acc #,(first vars))
                      (rest vars)))))]
  #:with nested-τapps-pat (make-nested-τapps #'(base-type (? (λ (id) (free-identifier=? #'τ id)))))
  #:with nested-τapps-constructor (make-nested-τapps #'(base-type #'τ))
  (begin
    (define-syntax τ (base-type #'τ))
    (begin-for-syntax
      (define (τ-proc τ_arg ...)
        nested-τapps-constructor)
      (define-match-expander τ
        (syntax-parser
          [(_ {~var τ_arg id} ...)
           #'nested-τapps-pat])
        (make-variable-like-transformer #'τ-proc)))))

(define-base-type → #:arity 2)
(define-base-type Integer)
(define-base-type String)

;; ---------------------------------------------------------------------------------------------------
;; types

(begin-for-syntax
  (define/match (type->string τ)
    [((τvar α))
     (symbol->string (syntax-e α))]
    [((∀ αs τ))
     (format "(∀ ~a ~a)" (map #{symbol->string (syntax-e %)} αs) (type->string τ))]
    [((→ τa τb))
     (format "(→ ~a ~a)" (type->string τa) (type->string τb))]
    [((τ~ τa τb _))
     (format "(τ~~ ~a ~a)" (type->string τa) (type->string τb))]
    [((τapp τf τx))
     (format "(~a ~a)" (type->string τf) (type->string τx))]
    [((base-type id))
     (symbol->string (syntax-e id))])

  ; explicitly list all cases instead of having a fallback case to get better error messages when a
  ; new type representation is added
  (define type=?
    (match-lambda**
     [((τvar a) (τvar b))
      (free-identifier=? a b)]
     [((τvar _) _) #f]
     [(_ (τvar _)) #f]
     [((base-type a) (base-type b))
      (free-identifier=? a b)]
     [((base-type _) _) #f]
     [(_ (base-type _)) #f]
     [((τapp τf τx) (τapp τg τy))
      (and (type=? τf τg)
           (type=? τx τy))]
     [((τapp _ _) _) #f]
     [(_ (τapp _ _)) #f]))

  (define type-eval
    (syntax-parser
      #:context 'current-type-eval
      #:literals [∀]
      [τ:id
       (syntax-local-value #'τ)]
      [(∀ [α:id ...] τ)
       (∀ (attribute α) (type-eval #'τ))]
      [(τ a)
       (τapp (type-eval #'τ)
             (type-eval #'a))]
      [(τ a as ...)
       (type-eval
        #'((τ a) as ...))]))

  (define (typeof stx)
    (get-stx-prop/car stx ':))

  (define (assign-type stx τ)
    (set-stx-prop/preserved stx ': τ))

  (define-simple-macro (⊢ e {~datum :} τ)
    (assign-type #`e (type-eval #`τ)))

  ; Generates a fresh type variable.
  (define (fresh) (τvar (generate-temporary)))

  (define (infer+erase stx #:ctx [ctx '()])
    (define wrapped-stx
      (match ctx
        [(list (cons xs τs) ...)
         (define/syntax-parse [x ...] xs)
         (define/syntax-parse [x- ...]
           (for/list ([x-stx (in-list xs)])
             (let ([tmp (generate-temporary x-stx)])
               (datum->syntax tmp (syntax-e tmp) x-stx))))
         ; We can’t directly embed types into syntax, since they are literal data, and quoting them
         ; messes up syntax objects inside of prefab structs. Instead, we can cheat by attaching a
         ; syntax property containing the type to a syntax object, then pull it off using typeof
         ; before calling instantiate-type.
         (define/syntax-parse [τ: ...]
           (for/list ([τ (in-list τs)])
             (syntax-property #'prop-holder ': τ)))
         #`(λ- (x- ...)
               (let-syntax ([x (make-variable-like-transformer/thunk
                                (λ () (assign-type #'x- (instantiate-type (typeof #'τ:)))))]
                            ...)
                 #,stx))]))
    (define-values [τ xs- stx-]
      (syntax-parse (local-expand wrapped-stx 'expression null)
        #:literals [kernel:lambda kernel:let-values]
        [(kernel:lambda xs-
           (kernel:let-values _
             (kernel:let-values _ body)))
         (values (typeof #'body) #'xs- #'body)]))
    (values τ xs- stx-))

  (define-simple-macro (define/infer+erase [τ:id xs-pat stx-pat] args ...)
    #:with xs-tmp (generate-temporary #'xs-pat)
    #:with stx-tmp (generate-temporary #'stx-pat)
    (begin
      (define-values [τ xs-tmp stx-tmp] (infer+erase args ...))
      (define/syntax-parse xs-pat xs-tmp)
      (define/syntax-parse stx-pat stx-tmp)))

  ; Given a type, replaces universally quantified type variables with fresh type variables.
  (define instantiate-type
    (match-lambda
      [(∀ αs τ)
       (apply-subst
        (make-immutable-free-id-table
         (for/list ([var (in-list αs)])
           (cons var (fresh))))
        τ)]
      [τ τ]))

  ; Given a type, finds all free type variables and universally quantifies them using ∀.
  (define (generalize-type τ)
    (define collect-vars
      (match-lambda
        [(τvar α)
         (list α)]
        [(τapp τf τx)
         (remove-duplicates (append (collect-vars τf)
                                    (collect-vars τx))
                            free-identifier=?)]
        [(base-type _)
         '()]))
    (let ([free-vars (collect-vars τ)])
      (if (empty? free-vars) τ
          (∀ free-vars τ)))))

;; ---------------------------------------------------------------------------------------------------
;; constraints & substitution

(begin-for-syntax
  ; Attaches a constraint to a syntax object by associating a type with the 'constraint syntax
  ; property. Calls syntax-local-introduce and type-eval on the provided constraint.
  (define (assign-constraint stx τa τb)
    (syntax-property stx 'constraints (list (τ~ τa τb stx)) #t))

  ; Returns a list of all constraints in a syntax object by recursively collecting the values of the
  ; 'constraint syntax property.
  (define (collect-constraints stx)
    (collect-properties stx 'constraints))

  ; The empty substitution set.
  (define empty-subst
    (make-immutable-free-id-table))

  ; Creates a substitution set containing exactly one subsitution between the given type variable and
  ; the given type.
  (define (bind-subst τv τ)
    (make-immutable-free-id-table
     (list (cons τv τ))))

  ; Composes two substitution sets by applying one substitution set to the other and taking their
  ; union.
  (define (compose-substs a b)
    (free-id-table-union
     (make-immutable-free-id-table
      (for/list ([(k v) (in-free-id-table b)])
        (cons k (apply-subst a v))))
     a))

  ; Applies a subsitution set to a type or constraint by recursively replacing all substitutable type
  ; variables with their substitutions.
  (define (apply-subst subst τ)
    (let loop ([τ τ])
      (match τ
        [(τvar α)
         (free-id-table-ref subst α τ)]
        [(∀ αs τ)
         (∀ αs (loop τ))]
        [(τapp τf τx)
         (τapp (loop τf) (loop τx))]
        [(base-type _)
         τ]
        [(τ~ a b src)
         (τ~ (loop a) (loop b) src)])))

  ; Attempts to unify the two provided types, reporting errors in terms of the provided source syntax
  ; object.
  (define (unify τa τb #:src src)
    (if (type=? τa τb)
        empty-subst
        (match* (τa τb)
          [((τvar α) τ)
           (bind-subst α τ)]
          [(τ (τvar α))
           (bind-subst α τ)]
          [((→ τa τb) (→ τc τd))
           (unify* (list (cons τa τc)
                         (cons τb τd))
                   #:src src)]
          [(_ _)
           (raise-syntax-error #f (format "could not unify ~a with ~a"
                                          (type->string τa) (type->string τb))
                               src)])))

  ; Attempts to unify each pair of types provided, propagating the substitutions performed back into
  ; the set of constraints at each step.
  (define (unify* τ_pairs #:src src)
    (match τ_pairs
      ['() (make-immutable-free-id-table)]
      [(list (cons τa τb)
             (cons τas τbs) ...)
       (let* ([subst (unify τa τb #:src src)]
              [subst* (unify* (map cons (map #{apply-subst subst %} τas)
                                        (map #{apply-subst subst %} τbs))
                              #:src src)])
         (compose-substs subst subst*))]))

  ; Given a set of constraints, attempts to solve them with unification.
  (define (solve-constraints cs)
    (let loop ([cs cs]
               [subst empty-subst])
      (if (empty? cs) subst
          (match (first cs)
            [(τ~ τa τb src)
             (let ([subst* (unify τa τb #:src src)])
               (loop (map #{apply-subst subst* %} (rest cs))
                     (compose-substs subst* subst)))]))))

  ; Given a substitution set, recursively walks a syntax object and retroactively replaces ': syntax
  ; properties with their inferred types after unification. Also attaches a ':-string property, which
  ; contains the final value of ': converted to a string using type->string, which is useful for
  ; debugging.
  (define (apply-substitutions-to-types subst stx)
    (define (perform-substitution stx)
      (if (syntax-property stx ':)
          (let ([new-type (apply-subst subst (get-stx-prop/car stx ':))])
            (syntax-property (syntax-property stx ': new-type #t)
                             ':-string (type->string new-type)))
          stx))
    (let recur ([stx stx])
      (syntax-rearm
       (syntax-parse (syntax-disarm stx (current-code-inspector))
         [(elem . rest)
          (perform-substitution
           (datum->syntax this-syntax (cons (recur #'elem) (recur #'rest))
                          this-syntax this-syntax))]
         [_ (perform-substitution this-syntax)])
       stx))))

;; ---------------------------------------------------------------------------------------------------
;; typed forms

(define-syntax-parser λ
  [(_ x:id e:expr)
   #:do [(define τv (fresh))
         (define/infer+erase [τ [x-] e-] #'e #:ctx (list (cons #'x τv)))]
   (assign-type #'(λ- (x-) e-)
                (→ τv τ))])

(define-syntax-parser hash-percent-app
  [(_ fn arg)
   #:do [(define τv (fresh))
         (define/infer+erase [τ_fn [] fn-] #'fn)
         (define/infer+erase [τ_arg [] arg-] #'arg)]
   (assign-constraint (assign-type (syntax/loc this-syntax
                                     (#%app- fn- arg-))
                                   τv)
                      τ_fn (→ τ_arg τv))])

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

(define-syntax-parser let
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

;; ---------------------------------------------------------------------------------------------------
;; primitive operators

(define ((+/c a) b) (+- a b))
(define-syntax + (make-variable-like-transformer
                  (⊢ +/c : (→ Integer (→ Integer Integer)))))
