#lang curly-fn racket/base

(provide : λ let data case +
         → Integer String
         (rename-out [hash-percent-app #%app]
                     [hash-percent-datum #%datum]
                     [hash-percent-module-begin #%module-begin]))

(require (for-syntax macrotypes/stx-utils
                     racket/base
                     racket/format
                     racket/function
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
         (postfix-in - (combine-in racket/base
                                   racket/function
                                   racket/match
                                   racket/splicing))
         (prefix-in kernel: '#%kernel)
         syntax/parse/define)

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
             #'(define τ-proc nested-τapps-constructor)
             #'(define (τ-proc τ_arg ...)
                 nested-τapps-constructor))
  (begin
    (define-syntax τ (base-type #'τ constructors))
    (begin-for-syntax
      value-definition
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
     [(_ (τapp _ _)) #f]))

  (define type-eval
    (syntax-parser
      #:context 'type-eval
      #:literals [∀]
      [τ:id
       (syntax-local-value #'τ)]
      [(∀ [α:id ...] τ)
       (∀ (attribute α) (type-eval #'τ))]
      [(τ a)
       (τapp (type-eval #'τ)
             (type-eval #'a))]
      [(τ a as ...)
       (type-eval #'((τ a) as ...))]))

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
         (define/syntax-parse [τ-proxy ...] (map property-proxy τs))
         #`(λ- (x- ...)
               (let-syntax ([x (make-variable-like-transformer/thunk
                                (λ () (assign-type #'x- (instantiate-type
                                                         (property-proxy-value #'τ-proxy)))))]
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
  (define (assign-constraints stx τ-pairs)
    (syntax-property stx 'constraints (map #{τ~ (car %) (cdr %) stx} τ-pairs) #t))

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
;; general typed forms

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

;; ---------------------------------------------------------------------------------------------------
;; ADTs

(begin-for-syntax
  (define →/curried
    (match-lambda*
      [(list τa τb)
       (→ τa τb)]
      [(list τ τs ...)
       (→ τ (apply →/curried τs))]))

  (define-syntax-class data-constructor-spec
    #:attributes [tag [arg 1] len nullary?]
    #:description #f
    [pattern tag:id
             #:attr [arg 1] '()
             #:attr len 0
             #:attr nullary? #t]
    [pattern {~and norm (tag:id arg ...+)}
             #:attr len (length (attribute arg))
             #:attr nullary? #f]
    [pattern {~and (tag:id)
                   {~fail (~a "data constructors without arguments should not be enclosed in "
                              "parentheses; perhaps you meant ‘" (syntax-e #'tag) "’?")}}
             #:attr [arg 1] #f
             #:attr len #f
             #:attr nullary? #f])

  (struct data-constructor (macro base-type arg-types match-clause)
    #:property prop:procedure 0))

(define-syntax-parser define-data-constructor
  [(_ τ:id constructor:data-constructor-spec)
   #:with tag- (generate-temporary #'constructor.tag)
   #:with tag-/curried (generate-temporary #'constructor.tag)
   #:with [τ_arg-proxy ...] (map #{property-proxy (type-eval %)} (attribute constructor.arg))
   #:with [field ...] (generate-temporaries #'(constructor.arg ...))
   #`(begin-
       ; check if the constructor is nullary or not
       #,(if (attribute constructor.nullary?)
             ; if it is, just define a value
             #'(begin-
                 (define- tag-
                   (let- ()
                     (struct- constructor.tag () #:transparent)
                     (constructor.tag)))
                 (define-syntax constructor.tag
                   (data-constructor (make-variable-like-transformer
                                      (assign-type #'tag- τ))
                                     τ '() (λ (_) #'(==- tag-)))))
             ; if it isn’t, define a constructor function, but preserve the original `struct`-defined
             ; id as a syntax property (to be used with Racket’s `match`)
             #'(splicing-local- [(struct- tag- (field ...) #:transparent
                                   #:reflection-name 'constructor.tag)
                                 (define- tag-/curried (curry- tag-))]
                 (define-syntax constructor.tag
                   (data-constructor
                    (make-variable-like-transformer
                     (assign-type #'tag-/curried
                                  (→/curried (property-proxy-value #'τ_arg-proxy) ...
                                             τ)))
                    τ (list (property-proxy-value #'τ_arg-proxy) ...)
                    (λ (ids) #`(tag- . #,ids)))))))])

(define-syntax-parser data
  [(_ τ:id constructor:data-constructor-spec ...)
   #'(begin-
       (define-base-type τ #:constructors (list #'constructor ...))
       (define-data-constructor τ constructor) ...)])

(define-syntax-parser case
  [(_ val:expr [pat:data-constructor-spec body:expr] ...+)
   ; ensure all provided patterns are actual data constructors
   #:do [(define invalid-constructors
           (filter-not #{data-constructor? (syntax-local-value % (thunk #f))}
                       (attribute pat.tag)))]
   #:fail-unless (empty? invalid-constructors)
                 (if (= 1 (length invalid-constructors))
                     (~a (syntax-e (first invalid-constructors))
                         " is not bound to a data constructor")
                     (~a (identifiers->english-list invalid-constructors)
                         " are not bound to data constructors"))

   ; get the type we’re destructuring on
   #:do [(define data-constructors (map syntax-local-value (attribute pat.tag)))
         (define τ_required (data-constructor-base-type (first data-constructors)))
         (define/infer+erase [τ_val [] val-] #'val)]
   #:with [constructor:data-constructor-spec ...] (base-type-constructors τ_required)

   ; assert that all of the tags are actually constructors of τ_val
   #:do [(for ([pat-stx (in-list (attribute pat))]
               [pat-tag-stx (in-list (attribute pat.tag))])
           (unless (member pat-tag-stx (attribute constructor.tag) free-identifier=?)
             (raise-syntax-error #f (~a "‘" (syntax-e pat-tag-stx) "’ is not a visible constructor of"
                                        " ‘" (type->string τ_required) "’")
                                 this-syntax pat-stx)))]

   ; perform exhaustiveness checking
   #:do [(define missing-tags (filter-not #{member % (attribute pat.tag) free-identifier=?}
                                          (attribute constructor.tag)))]
   #:fail-unless (empty? missing-tags)
                 (~a "not all cases of type ‘" (type->string τ_required) "’ are accounted for "
                     "(missing " (identifiers->english-list missing-tags) ")")

   ; expand all the bodies
   #:do [(define-values [τ_bodies match-clauses]
           (for/lists [τ_bodies match-clauses]
                      ([pat-arg-ids (in-list (attribute pat.arg))]
                       [pat-arg-types (in-list (map data-constructor-arg-types data-constructors))]
                       [body-stx (in-list (attribute body))]
                       [make-match-clause (in-list (map data-constructor-match-clause
                                                        data-constructors))])
             (define-values [τ_body pat-arg-ids- body-stx-]
               (infer+erase body-stx #:ctx (map cons pat-arg-ids pat-arg-types)))
             (values τ_body #`(#,(make-match-clause pat-arg-ids-) #,body-stx-))))]

   ; add constraints that ensure all bodies produce the same type
   (assign-constraints (assign-type (quasisyntax/loc this-syntax
                                      (match- val- #,@match-clauses))
                                    (first τ_bodies))
                       (map #{cons (first τ_bodies) %} (rest τ_bodies)))])

;; ---------------------------------------------------------------------------------------------------
;; primitive operators

(define ((+/c a) b) (+- a b))
(define-syntax + (make-variable-like-transformer
                  (⊢ +/c : (→ Integer (→ Integer Integer)))))
