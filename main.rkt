#lang curly-fn racket/base

(provide : λ let letrec data case _
         ∀ → Integer String
         + - *
         (rename-out [hash-percent-app #%app]
                     [hash-percent-datum #%datum]
                     [hash-percent-module-begin #%module-begin]))

(require (for-syntax macrotypes/stx-utils
                     racket/base
                     racket/dict
                     racket/format
                     racket/function
                     racket/list
                     racket/match
                     racket/syntax
                     syntax/id-table
                     syntax/parse/class/local-value
                     syntax/parse/define
                     syntax/parse/experimental/specialize
                     "util/stx.rkt")
         (for-meta 2 racket/base
                     racket/syntax
                     syntax/transformer)
         (only-in macrotypes/typecheck
                  postfix-in type-error
                  get-stx-prop/car)
         (postfix-in - (combine-in racket/base
                                   racket/function
                                   racket/match
                                   racket/splicing))
         (prefix-in kernel: '#%kernel)
         syntax/parse/define)

(module+ internal
  (provide (for-syntax solve-constraints τ~ → τvar τvar-id)
           define-base-type))

;; ---------------------------------------------------------------------------------------------------
;; module reader

(module reader syntax/module-reader rascal)

;; ---------------------------------------------------------------------------------------------------
;; type constructors

(begin-for-syntax
  (struct ∀ (τvars τ) #:prefab)
  (struct τ~ (a b src) #:prefab)
  (struct base-type (id constructors) #:prefab)
  (struct τvar (id) #:prefab)
  (struct τapp (τ arg) #:prefab))

(define-syntax (∀ stx) (raise-syntax-error #f "∀ cannot be used as an expression" stx))

(define-simple-macro (define-base-type τ:id
                       {~or {~optional {~seq #:arity arity:nat}
                                       #:defaults ([arity #'0])}
                            {~optional {~seq #:constructors constructors:expr}
                                       #:defaults ([constructors #'#f])}}
                       ...)
  #:with τ-value (generate-temporary #'τ)
  #:with [τ_arg ...] (generate-temporaries (make-list (syntax-e #'arity) #f))
  #:do [(define (make-nested-τapps base-stx)
          (let loop ([acc base-stx]
                     [vars (attribute τ_arg)])
            (if (empty? vars) acc
                (loop #`(τapp #,acc #,(first vars))
                      (rest vars)))))]
  #:with nested-τapps-pat (make-nested-τapps #'(base-type (? (λ (id) (free-identifier=? #'τ id))) _))
  #:with nested-τapps-constructor (make-nested-τapps #'(base-type #'τ constructors))
  #:with value-definition
         (if (zero? (syntax-e (attribute arity)))
             #'(define τ-value nested-τapps-constructor)
             #'(define (τ-value τ_arg ...)
                 nested-τapps-constructor))
  (begin
    (define-syntax τ (base-type #'τ constructors))
    (begin-for-syntax
      value-definition
      (define-match-expander τ
        (syntax-parser
          [(_ {~var τ_arg id} ...)
           #'nested-τapps-pat])
        (make-variable-like-transformer #'τ-value)))))

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
    [((base-type id _))
     (symbol->string (syntax-e id))])

  ; explicitly list all cases instead of having a fallback case to get better error messages when a
  ; new type representation is added
  (define type=?
    (match-lambda**
     [((τvar a) (τvar b))
      (free-identifier=? a b)]
     [((τvar _) _) #f]
     [(_ (τvar _)) #f]
     [((base-type a _) (base-type b _))
      (free-identifier=? a b)]
     [((base-type _ _) _) #f]
     [(_ (base-type _ _)) #f]
     [((τapp τf τx) (τapp τg τy))
      (and (type=? τf τg)
           (type=? τx τy))]
     [((τapp _ _) _) #f]
     [(_ (τapp _ _)) #f]
     [({and τa (∀ αs _)} {and τb (∀ βs _)})
      (and (= (length αs) (length βs))
           (let ([τvars (map fresh αs)])
             (type=? (instantiate-type-with τa τvars)
                     (instantiate-type-with τb τvars))))]))

  (define current-type-var-environment
    (make-parameter (make-immutable-free-id-table)))

  (define (extend-type-var-environment ctx [env (current-type-var-environment)])
    (for/fold ([env env])
              ([(id τ) (in-dict ctx)])
      (free-id-table-set env id τ)))

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
                 (define α-ids (map τvar-id α-types))]
           (∀ α-ids (type-eval #'τ #:ctx (map cons (attribute α) α-types)))]
          [(τ a)
           (τapp (loop #'τ)
                 (loop #'a))]
          [(τ a as ...)
           (loop #'((τ a) as ...))]))))

  (define (typeof stx)
    (get-stx-prop/car stx ':))

  (define (assign-type stx τ)
    (set-stx-prop/preserved stx ': τ))

  (define-simple-macro (⊢ e {~datum :} τ)
    (assign-type #`e (type-eval #`τ)))

  ; Generates a fresh type variable.
  (define (fresh [base 'g])
    (τvar (generate-temporary base)))

  ; Like infers+erase, but for a single syntax object instead of a list.
  (define (infer+erase stx #:ctx [ctx '()])
    (define-values [τs xs- stxs-]
      (infers+erase (list stx) #:ctx ctx))
    (values (first τs) xs- (first stxs-)))

  ; Like define/infers+erase, but with the single syntax object behavior of infer+erase.
  (define-simple-macro (define/infer+erase [τ xs-pat stx-pat] args ...)
    #:with xs-tmp (generate-temporary #'xs-pat)
    #:with stx-tmp (generate-temporary #'stx-pat)
    (begin
      (match-define-values [τ xs-tmp stx-tmp] (infer+erase args ...))
      (define/syntax-parse xs-pat xs-tmp)
      (define/syntax-parse stx-pat stx-tmp)))

  ; The main inference function. Expands all of stxs within the context of ctx. This function does
  ; three main things:
  ;
  ;  1. It invokes local-expand on each of the syntax objects provided to it. Before calling
  ;     local-expand, it binds each of the identifiers in ctx to a syntax transformer that expands
  ;     to a reference to a fresh location, with the type provided in ctx attached as a syntax
  ;     property.
  ;
  ;  2. After expansion, it collects the types of the resulting syntax objects into a list.
  ;     Additionally, it collects the identifiers used to create fresh locations into a list, which
  ;     must be put in scope by the caller of infers+erase so that they are accessible by the bodies.
  ;
  ;     These three things (expanded syntax objects, result types, and fresh identifiers) are returned
  ;     from infers+erase as three return values, in the following order:
  ;
  ;       (values types fresh-ids expanded-stxs)
  ;
  ;  3. Finally, infers+erase also automatically attaches disappeared-use and disappeared-binding
  ;     syntax properties as necessary in order to cooperate with Check Syntax. (This is necessary
  ;     since the identifiers used in the source syntax are erased and replaced with the generated
  ;     fresh locations mentioned earlier.)
  ;
  ;    (listof syntax?)
  ;    (listof (cons/c identifier? type?))
  ; -> (values (listof type?)
  ;            (listof identifier?)
  ;            (listof syntax?))
  (define (infers+erase stxs #:ctx [ctx '()])
    (define-values [wrapped-stx disappeared-bindings]
      (match ctx
        [(list (cons xs τs) ...)
         (define/syntax-parse [x ...] xs)
         (define/syntax-parse [x- ...]
           (for/list ([x-stx (in-list xs)])
             (let ([tmp (generate-temporary x-stx)])
               (propagate-original-for-check-syntax
                (syntax-local-introduce x-stx)
                (datum->syntax tmp (syntax-e tmp) x-stx x-stx)))))
         (define/syntax-parse [x-introduced ...] (map syntax-local-introduce (attribute x-)))
         (define/syntax-parse [τ-proxy ...] (map property-proxy τs))
         (values
          #`(λ- (x- ...)
                (let-syntax ([x (make-variable-like-transformer/thunk
                                 (λ (id) (syntax-property
                                          (assign-type #'x- (instantiate-type
                                                             (property-proxy-value #'τ-proxy)))
                                          'disappeared-use
                                          (list (propagate-original-for-check-syntax
                                                 (syntax-local-introduce id)
                                                 (datum->syntax #'x-introduced
                                                                (syntax-e #'x-introduced)
                                                                id id))))))]
                             ...)
                  #,@stxs))
          (attribute x-))]))
    (define-values [τs xs- stxs-]
      (syntax-parse (local-expand wrapped-stx 'expression null)
        #:literals [kernel:lambda kernel:let-values]
        [(kernel:lambda xs-
           (kernel:let-values _
             (kernel:let-values _ bodies ...)))
         (values (map typeof (attribute bodies)) #'xs-
                 (map #{syntax-property % 'disappeared-binding disappeared-bindings}
                      (attribute bodies)))]))
    (values τs xs- stxs-))

  ; A helper macro for making it easier to consume the results of infers+erase. Since infers+erase
  ; produces three values, two of which are syntax, it is useful to bind the syntax values to pattern
  ; variables that cooperate with `syntax`, which this macro automatically does. Additionally, it
  ; binds the single value result, the types, in a position that accepts `match` patterns.
  (define-simple-macro (define/infers+erase [τs xs-pat stxs-pat] args ...)
    #:with xs-tmp (generate-temporary #'xs-pat)
    #:with stxs-tmp (generate-temporary #'stxs-pat)
    (begin
      (match-define-values [τs xs-tmp stxs-tmp] (infers+erase args ...))
      (define/syntax-parse xs-pat xs-tmp)
      (define/syntax-parse stxs-pat stxs-tmp)))

  ; Given a type, replaces universally quantified type variables with fresh type variables.
  (define instantiate-type
    (match-lambda
      [(∀ αs τ)
       (apply-subst
        (make-immutable-free-id-table
         (for/list ([var (in-list αs)])
           (cons var (fresh var))))
        τ)]
      [τ τ]))

  ; Instantiates a type with a particular set of type variables. It is the responsibility of the
  ; caller to ensure the provided type variables are unique.
  (define (instantiate-type-with τ τvars)
    (match τ
      [(∀ αs τ)
       (unless (= (length αs) (length τvars))
         (raise-arguments-error 'instantiate-type-with
                                (~a "the number of provided type variables does not match the number "
                                    "of quantified type variables in the provided type")
                                "τ" τ
                                "τvars" τvars))
       (apply-subst
        (make-immutable-free-id-table
         (for/list ([α (in-list αs)]
                    [τvar (in-list τvars)])
           (cons α τvar)))
        τ)]))

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
        [(base-type _ _)
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

  ; Like assign-constraint, but accepts a list of pairs and produces a set of constraints instead of a
  ; single contraint.
  (define (assign-constraints stx τ-pairs #:existing-constraints [existing-cs '()])
    (syntax-property stx 'constraints
                     (append (map #{τ~ (car %) (cdr %) stx} τ-pairs)
                             existing-cs)
                     #t))

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
        [(base-type _ _)
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
          [((τapp τa τb) (τapp τc τd))
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
         (compose-substs subst* subst))]))

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
;; ADTs

(begin-for-syntax
  (define →/curried
    (match-lambda*
      [(list τa τb)
       (→ τa τb)]
      [(list τ τs ...)
       (→ τ (apply →/curried τs))]))

  ; like →/curried, but interprets (→ τ) as τ
  (define →/curried*
    (match-lambda*
      [(list τ) τ]
      [other (apply →/curried other)]))

  (define-syntax-class type-constructor-spec
    #:attributes [tag [arg 1] len nullary?]
    #:description #f
    [pattern tag:id
             #:attr [arg 1] '()
             #:attr len 0
             #:attr nullary? #t]
    [pattern (tag:id arg:id ...+)
             #:attr len (length (attribute arg))
             #:attr nullary? #f]
    [pattern {~and (tag:id)
                   {~fail (~a "types without arguments should not be enclosed in parentheses; perhaps"
                              " you meant ‘" (syntax-e #'tag) "’?")}}
             #:attr [arg 1] #f
             #:attr len #f
             #:attr nullary? #f])

  (define-syntax-class data-constructor-spec
    #:attributes [tag [arg 1] len nullary?]
    #:description #f
    [pattern tag:id
             #:attr [arg 1] '()
             #:attr len 0
             #:attr nullary? #t]
    [pattern (tag:id arg ...+)
             #:attr len (length (attribute arg))
             #:attr nullary? #f]
    [pattern {~and (tag:id)
                   {~fail (~a "data constructors without arguments should not be enclosed in "
                              "parentheses; perhaps you meant ‘" (syntax-e #'tag) "’?")}}
             #:attr [arg 1] #f
             #:attr len #f
             #:attr nullary? #f])

  (struct data-constructor (macro type match-clause)
    #:property prop:procedure 0)

  (define (data-constructor-base-type constructor)
    (define get-base-type
      (match-lambda
        [(→ τa τb)
         (get-base-type τb)]
        [τ τ]))
    (match (data-constructor-type constructor)
      [(∀ αs τ) (get-base-type τ)]
      [τ        (get-base-type τ)]))

  (define (data-constructor-arg-types constructor)
    (define get-arg-types
      (match-lambda
        [(→ τa τb)
         (cons τa (get-arg-types τb))]
        [τ '()]))
    (match (data-constructor-type constructor)
      [(∀ αs τ) (get-arg-types τ)]
      [τ        (get-arg-types τ)]))

  (define (data-constructor-arity constructor)
    (length (data-constructor-arg-types constructor)))

  (define-syntax-class/specialize data-constructor-val
    (local-value data-constructor? #:failure-message "not bound as a data constructor"))

  (struct pat-base (stx) #:transparent)
  (struct pat-var pat-base (id) #:transparent)
  (struct pat-hole pat-base () #:transparent)
  (struct pat-con pat-base (constructor pats) #:transparent)

  (define-syntax-class pat
    #:description "a pattern"
    #:attributes [pat disappeared-uses]
    #:literals [_]
    [pattern {~and constructor:data-constructor-val ~!}
             #:do [(define val (attribute constructor.local-value))
                   (define arity (data-constructor-arity val))]
             #:fail-unless (zero? arity)
                           (~a "cannot match ‘" (syntax-e #'constructor) "’ as a value; it is a "
                               "constructor with arity " arity)
             #:attr pat (pat-con this-syntax val '())
             #:attr disappeared-uses (list (syntax-local-introduce #'constructor))]
    [pattern (constructor:data-constructor-val ~! arg:pat ...+)
             #:do [(define val (attribute constructor.local-value))
                   (define arity (data-constructor-arity val))]
             #:fail-when (zero? arity)
                         (~a "cannot match ‘" (syntax-e #'constructor) "’ as a constructor; it is a "
                             "value and should not be enclosed with parentheses")
             #:fail-when {(length (attribute arg)) . < . arity}
                         (~a "not enough arguments provided for constructor ‘"
                             (syntax-e #'constructor) "’, which has arity " arity)
             #:fail-when {(length (attribute arg)) . > . arity}
                         (~a "too many arguments provided for constructor ‘"
                             (syntax-e #'constructor) "’, which has arity " arity)
             #:attr pat (pat-con this-syntax (attribute constructor.local-value) (attribute arg.pat))
             #:attr disappeared-uses (list* (syntax-local-introduce #'constructor)
                                            (append* (attribute arg.disappeared-uses)))]
    [pattern _
             #:attr pat (pat-hole this-syntax)
             #:attr disappeared-uses (list (syntax-local-introduce this-syntax))]
    [pattern id:id
             #:attr pat (pat-var this-syntax #'id)
             #:attr disappeared-uses '()])

  ; Given a pattern, calculates the set of bindings, the type the pattern will match against, and the
  ; set of required constraints. Also creates a function that will produce a Racket `match` pattern
  ; given a set of binding identifiers.
  ;
  ; pat? -> (listof (cons/c identifier? type?)) type? (listof constraint?)
  ;         ((listof identifier?) -> syntax? (listof identifier?))
  (define infer+erase-pattern
    (match-lambda
      [(pat-var _ id)
       (let ([α (fresh)])
         (values (list (cons id α)) α '()
                 (match-lambda [(list* id rest) (values id rest)])))]
      [(pat-hole _)
       (let ([α (fresh)])
         (values '() α '()
                 (λ (ids) (values #'_ ids))))]
      [(pat-con stx constructor pats)
       (define-values [ctxs τs cs mk-pats] (infer+erase-patterns pats))
       (let* ([α (fresh)]
              [τ_fn (apply →/curried* (append τs (list α)))]
              [τ_con (instantiate-type (data-constructor-type constructor))])
         (values ctxs α (list* (τ~ τ_fn τ_con stx) cs)
                 (λ (ids) (let-values ([(match-pats rest) (mk-pats ids)])
                            (values ((data-constructor-match-clause constructor) match-pats)
                                    rest)))))]))

  ; Like infer+erase-pattern but for multiple patterns. Properly handles applying the `match` pattern
  ; constructors of each pattern to the provided list of identifiers.
  (define (infer+erase-patterns pats)
    (define-values [ctxs τs cs mk-pats]
      (for/lists [ctxs τs cs mk-pats]
                 ([pat (in-list pats)])
        (infer+erase-pattern pat)))
    (values (append* ctxs) τs cs
            (λ (ids) (for/fold ([match-pats '()]
                                [rest ids])
                               ([mk-pat (in-list mk-pats)])
                       (let-values ([(match-pat rest*) (mk-pat rest)])
                         (values (append match-pats (list match-pat)) rest*)))))))

(define-syntax-parser define-data-constructor
  [(_ τ:type-constructor-spec constructor:data-constructor-spec)
   #:with tag- (generate-temporary #'constructor.tag)
   #:with tag-/curried (generate-temporary #'constructor.tag)
   #:do [(define αs (map fresh (attribute τ.arg)))
         (define type-ctx (map cons (attribute τ.arg) αs))]
   #:with [α-proxy ...] (map property-proxy αs)
   #:with [τ_arg-proxy ...] (map #{property-proxy (type-eval % #:ctx type-ctx)}
                                 (attribute constructor.arg))
   #:with τ_result (if (attribute τ.nullary?) #'τ.tag
                       #'(τ.tag (property-proxy-value #'α-proxy) ...))
   #:with [field ...] (generate-temporaries #'(constructor.arg ...))
   #`(begin-
       ; check if the constructor is nullary or not
       #,(if (attribute constructor.nullary?)
             ; if it is, just define a value
             #'(begin-
                 (define- tag-
                   (let- ()
                     (struct- constructor.tag ())
                     (constructor.tag)))
                 (define-syntax constructor.tag
                   (let ([τ_val (generalize-type τ_result)])
                     (data-constructor
                      (make-variable-like-transformer/thunk
                       (thunk (assign-type #'tag- (instantiate-type τ_val))))
                      τ_val (match-lambda [(list) #'(==- tag-)])))))
             ; if it isn’t, define a constructor function, but preserve the original `struct`-defined
             ; id as a syntax property (to be used with Racket’s `match`)
             #'(splicing-local- [(struct- tag- (field ...) #:transparent
                                   #:reflection-name 'constructor.tag)
                                 (define- tag-/curried (curry- tag-))]
                 (define-syntax constructor.tag
                   (let ([τ_fn (generalize-type (→/curried (property-proxy-value #'τ_arg-proxy) ...
                                                           τ_result))])
                     (data-constructor
                      (make-variable-like-transformer/thunk
                       (thunk (assign-type #'tag-/curried (instantiate-type τ_fn))))
                      τ_fn (λ (ids) #`(tag- . #,ids))))))))])

(define-syntax-parser data
  [(_ τ:type-constructor-spec constructor:data-constructor-spec ...)
   #:with τ-arity (length (attribute τ.arg))
   #'(begin-
       (define-base-type τ.tag
         #:arity τ-arity
         #:constructors (list #'constructor ...))
       (define-data-constructor τ constructor) ...)])

(define-syntax-parser case
  [(_ val:expr {~describe "a pattern-matching clause"
                          [pat:pat body:expr]} ...+)
   ; expand the value and all the bodies
   #:do [(define/infer+erase [τ_val [] val-] #'val)
         (match-define-values [τ_pats τ_bodies {app append* cs} match-clauses]
           (for/lists [τ_pats τ_bodies css match-clauses]
                      ([pat-val (in-list (attribute pat.pat))]
                       [body-stx (in-list (attribute body))])
             (define-values [ctx τ_pat cs mk-match-pat] (infer+erase-pattern pat-val))
             (define/infer+erase [τ_body [x- ...] body-] body-stx #:ctx ctx)
             (match-define-values [match-pat (list)] (mk-match-pat (attribute x-)))
             (values τ_pat τ_body cs #`[#,match-pat body-])))]

   ; add constraints that ensure that the value being matched is consistent with the provided patterns
   ; and that all clause bodies produce the same type
   (assign-constraints (assign-type (syntax-property (quasisyntax/loc this-syntax
                                                       (match- val- #,@match-clauses))
                                                     'disappeared-use
                                                     (attribute pat.disappeared-uses))
                                    (first τ_bodies))
                       (append (map #{cons τ_val %} τ_pats)
                               (map #{cons (first τ_bodies) %} (rest τ_bodies)))
                       #:existing-constraints cs)])

;; ---------------------------------------------------------------------------------------------------
;; primitive operators

(define-simple-macro (define-primop id:id [e:expr {~datum :} τ])
  (define-syntax id (make-variable-like-transformer (⊢ e : τ))))

(define ((+/c a) b) (+- a b))
(define ((-/c a) b) (-- a b))
(define ((*/c a) b) (*- a b))

(define-primop + [+/c : (→ Integer (→ Integer Integer))])
(define-primop - [-/c : (→ Integer (→ Integer Integer))])
(define-primop * [*/c : (→ Integer (→ Integer Integer))])
