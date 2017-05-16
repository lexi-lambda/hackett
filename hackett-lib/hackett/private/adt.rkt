#lang curly-fn racket/base

(require racket/require hackett/private/util/require)

(require (for-syntax (multi-in racket [base contract format list match syntax])
                     (multi-in syntax/parse [class/local-value experimental/specialize])

                     hackett/private/util/list
                     hackett/private/util/stx)

         (postfix-in - (multi-in racket [base match splicing]))
         syntax/parse/define

         (except-in hackett/private/base @%app)
         (only-in hackett/private/kernel [#%app @%app]))

(provide (for-syntax data-constructor-spec)
         data case)

(begin-for-syntax
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

  (struct data-constructor (macro type make-match-pat)
    #:property prop:procedure 0)

  (define-syntax-class/specialize data-constructor-val
    (local-value data-constructor? #:failure-message "not bound as a data constructor"))

  ; Given a curried function type, produce a list of uncurried arguments and the result type. If the
  ; function is quantified, the type will be instantiated with fresh existentials.
  ;
  ; Example:
  ;   > (function-type-args/result (∀ a (-> a (-> B (C a)))))
  ;   (list a^ B)
  ;   (C a^)
  (define/contract (function-type-args/result! t)
    (-> τ? (values (listof τ?) τ?))
    (define instantiate-quantifiers
      (match-lambda
        [(τ:∀ x t) (let* ([x^ (generate-temporary x)]
                          [t* (inst t x (τ:var^ x^))])
                     (modify-type-context #{snoc % (ctx:var^ x^)})
                     (instantiate-quantifiers t*))]
        [t t]))
    (let flatten-fn ([t (instantiate-quantifiers t)])
      (match t
        [(τ:->* a b) (let-values ([(args result) (flatten-fn b)])
                       (values (cons a args) result))]
        [_ (values '() t)])))

  (define/contract (function-type-arity t)
    (-> τ? exact-integer?)
    (define strip-quantifiers
      (match-lambda
        [(τ:∀ _ t) (strip-quantifiers t)]
        [t t]))
    (define fn-depth
      (match-lambda
        [(τ:->* _ t) (add1 (fn-depth t))]
        [_ 0]))
    (fn-depth (strip-quantifiers t)))

  (define/contract (data-constructor-args/result! ctor)
    (-> data-constructor? (values (listof τ?) τ?))
    (function-type-args/result! (data-constructor-type ctor)))

  (define/contract (data-constructor-arity ctor)
    (-> data-constructor? exact-integer?)
    (function-type-arity (data-constructor-type ctor)))

  (struct pat-base (stx) #:transparent)
  (struct pat-var pat-base (id) #:transparent)
  (struct pat-hole pat-base () #:transparent)
  (struct pat-con pat-base (constructor pats) #:transparent)

  (define (pat? x) (or (pat-var? x) (pat-hole? x) (pat-con? x)))

  (define-syntax-class pat
    #:description "a pattern"
    #:attributes [pat disappeared-uses]
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
    [pattern {~literal _}
             #:attr pat (pat-hole this-syntax)
             #:attr disappeared-uses (list (syntax-local-introduce this-syntax))]
    [pattern id:id
             #:attr pat (pat-var this-syntax #'id)
             #:attr disappeared-uses '()])

  (define/contract (pat⇒! pat)
    (-> pat?
        (values
         τ?                                           ; the inferred type the pattern matches against;
         (listof ctx:assump?)                         ; the types of bindings produced by the pattern;
         (-> (listof identifier?)                     ; a function that produces a Racket `match`
             (values syntax? (listof identifier?))))) ; pattern given a set of binding ids
    (match pat
      [(pat-var _ id)
       (let ([a^ (generate-temporary)])
         (modify-type-context #{snoc % (ctx:var^ a^)})
         (values (τ:var^ a^) (list (ctx:assump id (τ:var^ a^)))
                 (match-lambda [(cons id rest) (values id rest)])))]
      [(pat-hole _)
       (let ([a^ (generate-temporary)])
         (modify-type-context #{snoc % (ctx:var^ a^)})
         (values (τ:var^ a^) '() #{values #'_ %}))]
      [(pat-con _ con pats)
       (let*-values ([(τs_args τ_result) (data-constructor-args/result! con)]
                     [(assumps mk-pats) (pats⇐! pats τs_args)])
         (values τ_result assumps
                 (λ (ids) (let-values ([(match-pats rest) (mk-pats ids)])
                            (values ((data-constructor-make-match-pat con) match-pats) rest)))))]))

  (define/contract (pat⇐! pat t)
    (-> pat? τ?
        (values (listof ctx:assump?) (-> (listof identifier?) (values syntax? (listof identifier?)))))
    (let-values ([(t_⇒ assumps mk-pat) (pat⇒! pat)])
      (τ<:! t_⇒ t)
      (values assumps mk-pat)))

  ; Combines a list of `match` pattern constructors to properly run them against a list of identifiers
  ; in sequence, then combine the results into a list of patterns. Used by pats⇐! and pats⇒!.
  (define/contract (combine-pattern-constructors mk-pats)
    (-> (listof (-> (listof identifier?) (values syntax? (listof identifier?))))
        (-> (listof identifier?) (values (listof syntax?) (listof identifier?))))
    (λ (ids) (for/fold ([match-pats '()]
                        [rest ids])
                       ([mk-pat (in-list mk-pats)])
               (let-values ([(match-pat rest*) (mk-pat rest)])
                 (values (snoc match-pats match-pat) rest*)))))

  (define/contract (pats⇒! pats)
    (-> (listof pat?)
        (values (listof τ?) (listof ctx:assump?)
                (-> (listof identifier?) (values (listof syntax?) (listof identifier?)))))
    (define-values [ts assumps mk-pats]
      (for/lists [ts assumps mk-pats]
                 ([pat (in-list pats)])
        (pat⇒! pat)))
    (values ts (append* assumps) (combine-pattern-constructors mk-pats)))

  (define/contract (pats⇐! pats ts)
    (-> (listof pat?) (listof τ?)
        (values (listof ctx:assump?)
                (-> (listof identifier?) (values (listof syntax?) (listof identifier?)))))
    (define-values [assumps mk-pats]
      (for/lists [assumps mk-pats]
                 ([pat (in-list pats)]
                  [t (in-list ts)])
        (pat⇐! pat t)))
    (values (append* assumps) (combine-pattern-constructors mk-pats))))

(define-syntax-parser define-data-constructor
  [(_ τ:type-constructor-spec constructor:data-constructor-spec)
   #:with tag- (generate-temporary #'constructor.tag)
   #:with tag-/curried (generate-temporary #'constructor.tag)
   #:with [α ...] (attribute τ.arg)
   ; calculate the result type of the data constructor, after being applied to args (if any)
   #:with τ_result (if (attribute τ.nullary?) #'τ.tag #'(@%app τ.tag α ...))
   ; calculate the type of the underlying constructor, with arguments, unquantified
   #:with τ_con_unquantified (foldr #{begin #`(@%app -> #,%1 #,%2)}
                                    #'τ_result
                                    (attribute constructor.arg))
   ; quantify the type using the type variables in τ, then evaluate the type
   #:with τ_con:type (foldr #{begin #`(∀ #,%1 #,%2)} #'τ_con_unquantified (attribute α))
   #:with τ_con-expr (preservable-property->expression (attribute τ_con.τ))
   #:with [field ...] (generate-temporaries (attribute constructor.arg))
   ; check if the constructor is nullary or not
   (if (attribute constructor.nullary?)
       ; if it is, just define a value
       #'(begin-
           (define- tag-
             (let- ()
               (struct- constructor.tag ())
               (constructor.tag)))
           (define-syntax- constructor.tag
             (data-constructor (make-typed-var-transformer #'tag- τ_con-expr) τ_con-expr
                               (match-lambda [(list) #'(==- tag-)]))))
       ; if it isn’t, define a constructor function
       #`(splicing-local- [(struct- tag- (field ...) #:transparent
                             #:reflection-name 'constructor.tag)
                           (define- #,(foldl #{begin #`(#,%2 #,%1)} #'tag-/curried (attribute field))
                             (tag- field ...))]
           (define-syntax- constructor.tag
             (data-constructor (make-typed-var-transformer #'tag-/curried τ_con-expr) τ_con-expr
                               (match-lambda [(list field ...) #`(tag- #,field ...)])))))])

(define-syntax-parser data
  [(_ τ:type-constructor-spec constructor:data-constructor-spec ...)
   #:with τ-base (generate-temporary #'τ.tag)
   #:with [τ-arg ...] (generate-temporaries (attribute τ.arg))
   #:with [τ-arg.τ ...] (map #{begin #`(attribute #,(format-id % "~a.τ" %))} (attribute τ-arg))
   #`(begin-
       (define-for-syntax- τ-base (τ:con #'τ.tag (list #'constructor ...)))
       (define-syntax τ.tag (make-type-variable-transformer τ-base))
       (define-data-constructor τ constructor) ...)])

(define-syntax-parser case
  [(_ val:expr {~describe "a pattern-matching clause" [pat:pat body:expr]} ...+)
   #:do [; infer the types of each clause
         (define-values [ts_pats match-pats- bodies- ts_bodies]
           (for/lists [ts_pats match-pats- bodies- ts_bodies]
                      ([body (in-list (attribute body))]
                       [pat (in-list (attribute pat.pat))])
             (match-let*-values (; infer the type the pattern will match against
                                 [(t_pat assumps mk-match-pat) (pat⇒! pat)]
                                 [(bindings) (map #{cons (ctx:assump-x %) (ctx:assump-t %)} assumps)]
                                 ; infer the type of the body expression
                                 [(bound-ids- body- t_body) (τ⇒/λ! body bindings)]
                                 ; construct a Racket `match` pattern from the case pattern
                                 [(match-pat- (list)) (mk-match-pat bound-ids-)])
               (values t_pat match-pat- body- t_body))))
         ; infer the type of the value being matched and ensure all the patterns can match against it
         (define val^ (generate-temporary))
         (modify-type-context #{snoc % (ctx:var^ val^)})
         (for-each #{τ<:! % (τ:var^ val^)} ts_pats)]
   #:with val- (τ⇐! #'val (apply-current-subst (τ:var^ val^)))
   #:do [; infer the result type and make sure it is a subtype of all case branches
         (define result^ (generate-temporary))
         (modify-type-context #{snoc % (ctx:var^ result^)})
         (for-each #{τ<:! % (τ:var^ result^)} ts_bodies)
         (define t_result (apply-current-subst (τ:var^ result^)))]
   #:with [match-pat- ...] match-pats-
   #:with [body- ...] bodies-
   (attach-type #'(match- val- [match-pat- body-] ...) t_result)])
