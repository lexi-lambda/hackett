#lang curly-fn racket/base

(require racket/require (only-in macrotypes/typecheck postfix-in))

(require (for-syntax (multi-in racket [base function format list match syntax])
                     (multi-in syntax/parse [class/local-value class/paren-shape experimental/specialize])
                     hackett/private/util/stx)
         (postfix-in - (multi-in racket [base function match splicing]))
         hackett/private/base
         syntax/parse/define)

(provide (for-syntax data-constructor-spec)
         data case)

;; ---------------------------------------------------------------------------------------------------
;; ADTs

(begin-for-syntax
  (define-syntax-class type-constructor-spec
    #:attributes [tag [arg 1] len nullary?]
    #:description #f
    [pattern tag:id
             #:attr [arg 1] '()
             #:attr len 0
             #:attr nullary? #t]
    [pattern (~braces ~! arg1:id tag:id arg2:id)
             #:attr [arg 1] (list #'arg1 #'arg2)
             #:attr len 2
             #:attr nullary? #f]
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
    [pattern (~braces ~! arg1 tag:id arg2)
             #:attr [arg 1] (list #'arg1 #'arg2)
             #:attr len 2
             #:attr nullary? #f]
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
   #:with [α-expr ...] (map preservable-property->expression αs)
   #:with [τ_arg-expr ...] (map #{preservable-property->expression (type-eval % #:ctx type-ctx)}
                                (attribute constructor.arg))
   #:with τ_result (if (attribute τ.nullary?) #'τ.tag
                       #'(τ.tag α-expr ...))
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
                   (let ([τ_fn (generalize-type (→/curried τ_arg-expr ... τ_result))])
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
