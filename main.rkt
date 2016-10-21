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
                     rascal/private/type
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

(define-simple-macro (define-primop id:id [e:expr {~literal :} τ])
  (define-syntax id (make-variable-like-transformer (⊢ e : τ))))

(define ((+/c a) b) (+- a b))
(define ((-/c a) b) (-- a b))
(define ((*/c a) b) (*- a b))

(define-primop + [+/c : (→ Integer (→ Integer Integer))])
(define-primop - [-/c : (→ Integer (→ Integer Integer))])
(define-primop * [*/c : (→ Integer (→ Integer Integer))])
