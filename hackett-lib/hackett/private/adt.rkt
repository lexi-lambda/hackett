#lang curly-fn racket/base

(require racket/require hackett/private/util/require hackett/private/type-reqprov

         (for-syntax (multi-in racket [base contract string format list match syntax])
                     (multi-in syntax/parse [class/local-value class/paren-shape
                                             experimental/template])
                     syntax/apply-transformer
                     threading

                     hackett/private/infix
                     hackett/private/prop-case-pattern-expander
                     hackett/private/util/list
                     hackett/private/util/stx)

         (postfix-in - (multi-in racket [base match promise splicing]))
         syntax/parse/define

         (except-in hackett/private/base @%app)
         (only-in hackett/private/class class-id derive-instance)
         (only-in hackett/private/kernel [λ plain-λ])
         (only-in (unmangle-types-in #:no-introduce (only-types-in hackett/private/kernel))
                  forall [#%app @%app]))

(provide (for-syntax type-constructor-spec data-constructor-spec
                     type-constructor-val data-constructor-val
                     data-constructor-field-types)
         (rename-out [λ lambda] [λ* lambda*])
         data case* case λ λ* defn _)

(begin-for-syntax
  (provide (contract-out [struct type-constructor ([type type?]
                                                   [arity exact-nonnegative-integer?]
                                                   [data-constructors (listof identifier?)]
                                                   [fixity (or/c operator-fixity? #f)])]
                         [struct data-constructor ([macro procedure?]
                                                   [type type?]
                                                   [make-match-pat procedure?]
                                                   [fixity (or/c operator-fixity? #f)])])))

(begin-for-syntax
  (define-splicing-syntax-class type-constructor-spec
    #:attributes [tag [arg 1] len nullary? fixity]
    #:commit
    #:description #f
    [pattern {~seq tag:id {~optional :fixity-annotation}}
             #:attr [arg 1] '()
             #:attr len 0
             #:attr nullary? #t]
    [pattern {~seq (~parens tag:id arg:id ...+) {~optional :fixity-annotation}}
             #:attr len (length (attribute arg))
             #:attr nullary? #f]
    [pattern {~seq {~braces a:id tag:id b:id} {~optional :fixity-annotation}}
             #:with [arg ...] #'[a b]
             #:attr len 2
             #:attr nullary? #f]
    [pattern {~and (tag:id)
                   {~fail (~a "types without arguments should not be enclosed in parentheses; perhaps"
                              " you meant ‘" (syntax-e #'tag) "’?")}}
             #:attr [arg 1] #f
             #:attr len #f
             #:attr nullary? #f
             #:attr fixity #f])

  (define-splicing-syntax-class data-constructor-spec
    #:attributes [tag [arg 1] len nullary? fixity]
    #:commit
    #:description #f
    [pattern {~seq tag:id {~optional :fixity-annotation}}
             #:attr [arg 1] '()
             #:attr len 0
             #:attr nullary? #t]
    [pattern {~seq (~parens tag:id arg ...+) {~optional :fixity-annotation}}
             #:attr len (length (attribute arg))
             #:attr nullary? #f]
    [pattern {~seq {~braces a tag:id b} {~optional :fixity-annotation}}
             #:with [arg ...] #'[a b]
             #:attr len 2
             #:attr nullary? #f]
    [pattern {~and (tag:id)
                   {~fail (~a "data constructors without arguments should not be enclosed in "
                              "parentheses; perhaps you meant ‘" (syntax-e #'tag) "’?")}}
             #:attr [arg 1] #f
             #:attr len #f
             #:attr nullary? #f
             #:attr fixity #f])

  (struct type-constructor (type arity data-constructors fixity)
    #:transparent
    #:property prop:procedure
    (λ (ctor stx) ((make-variable-like-transformer (type-constructor-type ctor)) stx))
    #:property prop:infix-operator (λ (ctor) (type-constructor-fixity ctor)))

  (struct data-constructor (macro type make-match-pat fixity)
    #:transparent
    #:property prop:procedure (struct-field-index macro)
    #:property prop:infix-operator (λ (ctor) (data-constructor-fixity ctor)))

  (define-syntax-class type-constructor-val
    #:attributes [local-value type arity data-constructors fixity]
    #:commit
    #:description #f
    [pattern
     {~var || (local-value type-constructor? #:failure-message "not bound as a type constructor")}
     #:attr type (type-constructor-type (attribute local-value))
     #:attr arity (type-constructor-arity (attribute local-value))
     #:attr data-constructors (type-constructor-data-constructors (attribute local-value))
     #:attr fixity (type-constructor-fixity (attribute local-value))])

  (define-syntax-class data-constructor-val
    #:attributes [local-value macro type make-match-pat fixity]
    #:commit
    #:description #f
    [pattern
     {~var || (local-value data-constructor? #:failure-message "not bound as a data constructor")}
     #:attr macro (data-constructor-macro (attribute local-value))
     #:attr type (data-constructor-type (attribute local-value))
     #:attr make-match-pat (data-constructor-make-match-pat (attribute local-value))
     #:attr fixity (data-constructor-fixity (attribute local-value))])

  ; Given a curried function type, produce a list of uncurried arguments and the result type. If the
  ; function is quantified, the type will be instantiated with fresh solver variables.
  ;
  ; Example:
  ;   > (function-type-args/result (∀ a (-> a (-> B (C a)))))
  ;   (list a^ B)
  ;   (C a^)
  (define/contract function-type-args/result!
    (-> type? (values (listof type?) type?))
    (syntax-parser
      #:context 'function-type-args/result!
      #:literal-sets [type-literals]
      [(~#%type:forall* [x ...] (~->* t ... r))
       #:with [x^ ...] (generate-temporaries (attribute x))
       #:do [(define inst-map (map cons (attribute x) (syntax->list #'[(#%type:wobbly-var x^) ...])))]
       (values (map #{insts % inst-map} (attribute t))
               (insts #'r inst-map))]))

  (define/contract function-type-arity
    (-> type? exact-integer?)
    (syntax-parser
      #:context 'function-type-arity
      #:literal-sets [type-literals]
      [(~#%type:forall* _ (~->* t ...))
       (sub1 (length (attribute t)))]))

  (define/contract (data-constructor-args/result! ctor)
    (-> data-constructor? (values (listof type?) type?))
    (function-type-args/result! (data-constructor-type ctor)))

  (define/contract (data-constructor-arity ctor)
    (-> data-constructor? exact-integer?)
    (function-type-arity (data-constructor-type ctor)))

  (define/contract (data-constructor-all-tags ctor)
    (-> data-constructor? (listof identifier?))
    (let ([t (data-constructor-type ctor)])
      (syntax-parse (data-constructor-type ctor)
        #:context 'data-constructor-all-tags
        #:literal-sets [type-literals]
        [(~#%type:forall* _ (~->* _ ... (~#%type:app* (#%type:con type-id) _ ...)))
         (type-constructor-data-constructors (syntax-local-value #'type-id))])))

  ; Given the type of a data constructor, returns the types of its fields, where all type variables
  ; are instantiated using the provided list of replacement types. Order of instantiation is
  ; consistent with the order of type arguments to the type constructor, so when fetching the fields
  ; for (Tuple a b), the first element of inst-tys will be used for a, and the second will be used
  ; for b. If the number of supplied replacement types is inconsistent with the number of arguments to
  ; the type constructor, a contract violation is raised.
  ;
  ; Example:
  ; > (data-constructor-field-types (list x^ y^)
  ;                                 (forall [b a] {a -> Integer -> (Maybe b) -> (Foo a b)}))
  ; (list x^ Integer (Maybe y^))
  ;
  ; While the data constructor type must be a fully-expanded type, the replacement types do not
  ; strictly need to be; they may be arbitrary syntax objects, in which case they will be left
  ; unexpanded in the result.
  (define/contract (data-constructor-field-types inst-tys con-ty)
    (-> (listof type?) type? (listof type?))
    (define/syntax-parse {~#%type:forall* [x ...] t_fn} con-ty)
    (define/syntax-parse
      {~->* t_arg ... {~#%type:app* ({~literal #%type:con} _) con-var:id ...}}
      #'t_fn)
    (unless (equal? (length (attribute x)) (length (attribute con-var)))
      (raise-arguments-error 'data-constructor-field-types
                             "unexpected number of quantified variables in constructor"
                             "quantified" (length (attribute x))
                             "constructor" (length (attribute con-var))))
    (unless (equal? (length (attribute con-var)) (length inst-tys))
      (raise-arguments-error 'data-constructor-field-types
                             (format "too ~a variables given for instantiation"
                                     (if (> (length (attribute con-var)) (length inst-tys))
                                         "few" "many"))
                             "expected" (length (attribute con-var))
                             "given" (length inst-tys)))
    (define var-subst (map cons (attribute con-var) inst-tys))
    (map #{insts % var-subst} (attribute t_arg)))

  (struct pat-base (stx) #:transparent)
  (struct pat-var pat-base (id) #:transparent)
  (struct pat-hole pat-base () #:transparent)
  (struct pat-con pat-base (constructor pats) #:transparent)
  (struct pat-str pat-base (str) #:transparent)
  (struct pat-int pat-base (int) #:transparent)
  (define pat? pat-base?)

  (define-syntax-class pat
    #:description "a pattern"
    #:attributes [pat disappeared-uses]
    #:commit

    [pattern {~and pat-exp
                   {~or pat-id (pat-id . _)}}
             #:declare pat-id (local-value case-pattern-expander?)
             #:do [(define trans
                     (case-pattern-expander-transformer (attribute pat-id.local-value)))]
             #:with :pat (local-apply-transformer trans #'pat-exp 'expression)]

    [pattern {~and constructor:data-constructor-val ~!}
             #:do [(define val (attribute constructor.local-value))
                   (define arity (data-constructor-arity val))]
             #:fail-unless (zero? arity)
                           (~a "cannot match ‘" (syntax-e #'constructor) "’ as a value; it is a "
                               "constructor with arity " arity)
             #:attr pat (pat-con this-syntax val '())
             #:attr disappeared-uses (list (syntax-local-introduce #'constructor))]
    [pattern (~parens constructor:data-constructor-val ~! arg:pat ...)
             #:do [(define val (attribute constructor.local-value))
                   (define arity (data-constructor-arity val))]
             #:fail-when {(length (attribute arg)) . < . arity}
                         (~a "not enough arguments provided for constructor ‘"
                             (syntax-e #'constructor) "’, which has arity " arity)
             #:fail-when {(length (attribute arg)) . > . arity}
                         (~a "too many arguments provided for constructor ‘"
                             (syntax-e #'constructor) "’, which has arity " arity)
             #:attr pat (pat-con this-syntax (attribute constructor.local-value) (attribute arg.pat))
             #:attr disappeared-uses (cons (syntax-local-introduce #'constructor)
                                           (append* (attribute arg.disappeared-uses)))]
    [pattern {~braces a:pat constructor:data-constructor-val b:pat}
             #:do [(define val (attribute constructor.local-value))
                   (define arity (data-constructor-arity val))]
             #:fail-when (zero? arity)
                         (~a "cannot match ‘" (syntax-e #'constructor) "’ infix; it is a value "
                             "and should matched as a bare identifier")
             #:fail-when (not (= arity 2))
                         (~a "cannot match ‘" (syntax-e #'constructor) "’ infix; it has arity "
                             arity ", but constructors matched infix must have arity 2")
             #:attr pat (pat-con this-syntax (attribute constructor.local-value)
                                 (list (attribute a.pat) (attribute b.pat)))
             #:attr disappeared-uses (cons (syntax-local-introduce #'constructor)
                                           (append (attribute a.disappeared-uses)
                                                   (attribute b.disappeared-uses)))]
    [pattern {~braces a:pat ctor:data-constructor-val b:pat
                      {~seq ctors:data-constructor-val bs:expr} ...}
             #:when (eq? 'left (data-constructor-fixity (attribute ctor.local-value)))
             #:with ~! #f
             #:fail-unless (andmap #{eq? % 'left}
                                   (map data-constructor-fixity (attribute ctors.local-value)))
                           (~a "cannot mix left- and right-associative operators in the same infix "
                               "pattern")
             #:with :pat (template {{a ctor b} {?@ ctors bs} ...})]
    [pattern {~braces {~seq as:expr ctors:data-constructor-val} ...
                      a:pat ctor:data-constructor-val b:pat}
             #:when (eq? 'right (data-constructor-fixity (attribute ctor.local-value)))
             #:and ~!
             #:fail-unless (andmap #{eq? % 'right}
                                   (map data-constructor-fixity (attribute ctors.local-value)))
                           (~a "cannot mix left- and right-associative operators in the same infix "
                               "pattern")
             #:with :pat (template {{?@ as ctors} ... {a ctor b}})]
    [pattern {~literal _}
             #:attr pat (pat-hole this-syntax)
             #:attr disappeared-uses (list (syntax-local-introduce this-syntax))]
    [pattern id:id
             #:attr pat (pat-var this-syntax #'id)
             #:attr disappeared-uses '()]
    [pattern str:str
             #:attr pat (pat-str this-syntax #'str)
             #:attr disappeared-uses '()]
    [pattern int:integer
             #:attr pat (pat-int this-syntax #'int)
             #:attr disappeared-uses '()])

  (define/contract (pat⇒! pat)
    (-> pat?
        (values
         type?                                        ; the inferred type the pattern matches against;
         (listof (cons/c identifier? type?))          ; the types of bindings produced by the pattern;
         (-> (listof identifier?)                     ; a function that produces a Racket `match`
             (values syntax? (listof identifier?))))) ; pattern given a set of binding ids
    (match pat
      [(pat-var _ id)
       (let ([a^ (generate-temporary)])
         (values #`(#%type:wobbly-var #,a^) (list (cons id #`(#%type:wobbly-var #,a^)))
                 (match-lambda [(cons id rest) (values id rest)])))]
      [(pat-hole _)
       (let ([a^ (generate-temporary)])
         (values #`(#%type:wobbly-var #,a^) '() #{values #'_ %}))]
      [(pat-str _ str)
       (values (expand-type #'String) '() #{values #`(app force- #,str) %})]
      [(pat-int _ int)
       (values (expand-type #'Integer) '() #{values #`(app force- #,int) %})]
      [(pat-con _ con pats)
       (let*-values ([(τs_args τ_result) (data-constructor-args/result! con)]
                     [(assumps mk-pats) (pats⇐! pats τs_args)])
         (values τ_result assumps
                 (λ (ids) (let-values ([(match-pats rest) (mk-pats ids)])
                            (values ((data-constructor-make-match-pat con) match-pats) rest)))))]))

  (define/contract (pat⇐! pat t)
    (-> pat? type?
        (values (listof (cons/c identifier? type?))
                (-> (listof identifier?) (values syntax? (listof identifier?)))))
    (let-values ([(t_⇒ assumps mk-pat) (pat⇒! pat)])
      (type<:! t_⇒ t #:src (pat-base-stx pat))
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
        (values (listof type?) (listof (cons/c identifier? type?))
                (-> (listof identifier?) (values (listof syntax?) (listof identifier?)))))
    (define-values [ts assumps mk-pats]
      (for/lists [ts assumps mk-pats]
                 ([pat (in-list pats)])
        (pat⇒! pat)))
    (values ts (append* assumps) (combine-pattern-constructors mk-pats)))

  (define/contract (pats⇐! pats ts)
    (-> (listof pat?) (listof type?)
        (values (listof (cons/c identifier? type?))
                (-> (listof identifier?) (values (listof syntax?) (listof identifier?)))))
    (define-values [assumps mk-pats]
      (for/lists [assumps mk-pats]
                 ([pat (in-list pats)]
                  [t (in-list ts)])
        (pat⇐! pat t)))
    (values (append* assumps) (combine-pattern-constructors mk-pats)))


  ;; -------------------------------------------------------------------------------------------------
  ;; Exhaustiveness checking

  (struct ideal-con (ctor-tag args))

  ; An “ideal” pattern represents unmatched patterns, used by the exhaustiveness checker.
  ; Specifically, the current set of ideals represents the minimal set of patterns that would cover
  ; all uncovered cases without covering covered ones. As the exhaustiveness checker runs, it consults
  ; user provided patterns, and adjusts the set of ideals accordingly: it eliminates covered ideals
  ; and splits partially-covered ideals into more specific ones.
  ;
  ; An ideal pattern can be a variable, which corresponds to a pat-var or pat-hole (that is, it
  ; matches anything), or a constructor, which contains sub-ideals for each argument to the
  ; constructor.
  (define ideal?
    (or/c symbol?      ; ideal variable
          ideal-con?)) ; ideal for specific constructor

  ; Creates a list of n fresh ideal variables.
  (define (generate-fresh-ideals n)
    (build-list n (λ (_) (gensym))))

  ; Returns a pretty representation of ideal. Uses “syntax-e” to turn constructor tags into strings,
  ; and replaces symbols with “_”.
  (define (ideal->string q)
    (define ideal->datum
      (match-lambda
        [(? symbol?)
         '_]
        [(ideal-con ctor-tag '())
         (syntax-e ctor-tag)]
        [(ideal-con ctor-tag qs)
         (cons (syntax-e ctor-tag)
               (map ideal->datum qs))]))
    (format "~a" (ideal->datum q)))

  ; Generates a new ideal-con from a data constructor’s tag identifier
  (define (constructor-tag->ideal-con ctor-tag)
    (define arity (data-constructor-arity (syntax-local-value ctor-tag)))
    (ideal-con ctor-tag (generate-fresh-ideals arity)))

  ; Returns a substition function f for the given ideal q such that (f r) is just like q, except that
  ; all occurences of x are replaced by r.
  (define (ideal->subst-fn q x)
    (match q
      [(== x eq?)
       (λ (r) r)]
      [(ideal-con ctor qs)
       (let ([fns (map #{ideal->subst-fn % x} qs)])
         (λ (r) (ideal-con ctor (map #{% r} fns))))]
      [_
       (λ (r) q)]))

  ; Substitutes occurences of symbol x with each ideal in rs, for each ideal in qs.
  ;
  ; e.g.
  ;   (subs 'A '(B C) (list 'D (con "*" 'A)))
  ;   =
  ;   (list (list 'D (con "*" 'B))
  ;         (list 'D (con "*" 'C)))
  (define (substitute-ideals x rs qs)
    (let ([subst-fns (map #{ideal->subst-fn % x} qs)])
      (for/list ([r (in-list rs)])
        (for/list ([fn (in-list subst-fns)])
          (fn r)))))

  (define current-exhaust-split-handler
    (make-parameter #f))

  ; Checks if the ideals are covered by the patterns. Returns #t if the ideals are fully covered, #f
  ; if some ideals are left uncovered, or a pair of a symbol and its replacements if it needs to be
  ; split.
  (define (check-ideals ideals pats)
    (for/fold ([acc #t])
              ([p (in-list pats)]
               [q (in-list ideals)])
      #:break (not (eq? #t acc))
      (match p
        ; The ideal is always satisfied when we hit a wildcard pattern, such as a variable or a hole,
        ; since they match everything.
        [(pat-var _ _) #t]
        [(pat-hole _) #t]

        ; When we hit a constructor pattern, we check the ideal. If it is a constructor, compare the
        ; tags and then recur for the sub-patterns. If it is a variable, then split the ideal into new
        ; ideals for each kind of constructor.
        [(pat-con _ ctor sub-pats)
         (match q
           [(ideal-con ctor-tag sub-ideals)
            (and (eq? (syntax-local-value ctor-tag) ctor)
                 (check-ideals sub-ideals sub-pats))]

           [(? symbol? x)
            (let ([split-into (map constructor-tag->ideal-con (data-constructor-all-tags ctor))])
              (cons x split-into))])]

        ; TODO: better exhaustiveness checking on strings. OCaml checks for the strings "*", "**",
        ; "***" etc. It would be fairly easy to do the same using splitting.
        [(pat-str _ s) #f]
        [(pat-int _ i) #f])))


  ; Checks if patterns are exhaustive or not. Given a list of pattern-lists, returns #f if no
  ; un-matched patterns are found. Otherwise, returns an example of an un-matched pattern-list.
  (define/contract (check-exhaustiveness patss pat-count)
    (-> (listof (listof pat?))
        exact-nonnegative-integer?
        (or/c #f (listof ideal?)))
    ; Initially, use a fresh ideal variable for each pattern.
    (let check ([idealss (list (generate-fresh-ideals pat-count))])
      (match idealss
        ; No more ideals to check; #f signals that the pattern is exhaustive.
        ['() #f]
        ; Check if the most recent ideal is exhaustive, or if it split into more ideals.
        [(cons ideals rest-idealss)
         (match (for/or ([pats (in-list patss)])
                 (check-ideals ideals pats))
           [#t
            (check rest-idealss)]
           ; Non-exhaustive! return un-matched ideals.
           [#f
            ideals]
           ; In case of split, substitute and append.
           [(cons x rs)
            (let ([new-idealss (substitute-ideals x rs ideals)])
              (check (append new-idealss rest-idealss)))])]))))

(define-syntax-parser define-data-constructor
  [(_ [τ:type-constructor-spec] [constructor:data-constructor-spec])
   #:with tag- (generate-temporary #'constructor.tag)
   #:with tag-/curried (generate-temporary #'constructor.tag)
   ; calculate the result type of the data constructor, after being applied to args (if any)
   #:with τ_result (if (attribute τ.nullary?) #'τ.tag #'(@%app τ.tag τ.arg ...))
   ; calculate the type of the underlying constructor, with arguments, unquantified
   #:with τ_con_unquantified (foldr #{begin #`(@%app -> #,%1 #,%2)}
                                    #'τ_result
                                    (map type-namespace-introduce (attribute constructor.arg)))
   ; quantify the type using the type variables in τ, then evaluate the type
   #:with τ_con:type #'(forall [τ.arg ...] τ_con_unquantified)
   #:with [field ...] (generate-temporaries (attribute constructor.arg))
   #:with fixity (attribute constructor.fixity)
   #`(begin-
       (define-values- [] τ_con.residual)
       ; check if the constructor is nullary or not
       #,(if (attribute constructor.nullary?)
             ; if it is, just define a value
             #'(begin-
                 (define- tag-
                   (let- ()
                     (struct- constructor.tag ())
                     (constructor.tag)))
                 (define-syntax- constructor.tag
                   (data-constructor
                    (make-typed-var-transformer #'tag- (quote-syntax τ_con.expansion))
                    (quote-syntax τ_con.expansion)
                    (match-lambda [(list) #'(app force- (==- tag-))])
                    'fixity)))
             ; if it isn’t, define a constructor function
             #`(splicing-local- [(struct- tag- (field ...) #:transparent
                                          #:reflection-name 'constructor.tag)
                                 (define- #,(foldl #{begin #`(#,%2 #,%1)}
                                                   #'tag-/curried
                                                   (attribute field))
                                   (tag- field ...))]
                 (define-syntax- constructor.tag
                   (data-constructor (make-typed-var-transformer #'tag-/curried
                                                                 (quote-syntax τ_con.expansion))
                                     (quote-syntax τ_con.expansion)
                                     (match-lambda [(list field ...)
                                                    #`(app force- (tag- #,field ...))])
                                     'fixity)))))])

(define-syntax-parser data
  [(_ τ:type-constructor-spec constructor:data-constructor-spec ...
      {~optional
       {~seq #:deriving [{~type {~var class-id (class-id #:require-deriving-transformer? #t)}} ...]}
       #:defaults ([[class-id 1] '()])})
   #:with [τ*:type-constructor-spec] (type-namespace-introduce #'τ)
   #:with fixity (attribute τ.fixity)
   #`(begin-
       (define-syntax- τ*.tag (type-constructor
                               #'(#%type:con τ*.tag)
                               '#,(attribute τ*.len)
                               (list #'constructor.tag ...)
                               'fixity))
       (define-data-constructor τ* constructor) ...
       (derive-instance class-id τ*.tag) ...)])

(begin-for-syntax
  (define-syntax-class (case*-clause num-pats)
    #:attributes [[pat 1] [pat.pat 1] pat.disappeared-uses body]
    #:description "a pattern-matching clause"
    [pattern [[p:pat ...+] body:expr]
             #:fail-unless (= (length (attribute p)) num-pats)
                           (~a "mismatch between number of patterns and number of values (expected "
                               num-pats " patterns, found " (length (attribute p)) ")")
             #:attr [pat 1] (attribute p)
             #:attr [pat.pat 1] (attribute p.pat)
             #:attr pat.disappeared-uses (attribute p.disappeared-uses)]))

(define-syntax-parser case*
  [(_ [val:expr ...+] {~var clause (case*-clause (length (attribute val)))} ...+)
   #:do [; Determine the type to use to unify all of the body clauses. If there is
         ; an expected type (from τ⇐/λ!), then use that type, otherwise generate a
         ; wobbly var that will be unified against each body type.
         (define t_body
           (or (get-expected this-syntax)
               #`(#%type:wobbly-var #,(generate-temporary #'body))))

         ; Infer the types of each clause and expand the bodies. Each clause has N patterns, each of
         ; which match against a particular type, and it also has a body, which must be typechecked
         ; as well. Additionally, inferring the pattern types produces a racket/match pattern, which
         ; we can use to implement the untyped expression.
         (define-values [tss_pats match-pats- bodies-]
           (for/lists [tss_pats match-pats- bodies-]
                      ([clause (in-list (attribute clause))]
                       [body (in-list (attribute clause.body))]
                       [pats (in-list (attribute clause.pat.pat))])
             (match-let*-values
                 ([; Infer the type each pattern will match against and collect the assumptions.
                   (ts_pats assumpss mk-match-pats)
                   (for/lists [ts_pats assumpss mk-match-pats]
                              ([pat (in-list pats)])
                     (pat⇒! pat))]
                  ; Collect the set of bindings introduced by the patterns.
                  [(assumps) (append* assumpss)]
                  ; Typecheck the body expression against the expected type.
                  [(bound-ids- body-) (τ⇐/λ! body t_body assumps)]
                  ; Use the bound ids to construct racket/match patterns from the case patterns.
                  [(match-pats- (list))
                   (for/fold ([match-pats- '()]
                              [bound-ids- bound-ids-])
                             ([mk-match-pat (in-list mk-match-pats)])
                     (let-values ([(match-pat- bound-ids-*) (mk-match-pat bound-ids-)])
                       (values (cons match-pat- match-pats-) bound-ids-*)))]
                  ; Collect the racket/match patterns into a single, multi-pattern clause.
                  [(match-pat-) (quasisyntax/loc clause
                                  (#,@(reverse match-pats-)))])
               ; Return all the results of the inference process.
               (values ts_pats match-pat- body-))))

         ; Now that we’ve inferred the types that each pattern can match against, we should infer the
         ; types of each value being matched and ensure that all the patterns match against it. In
         ; order to do this, we want to transpose the list of inferred pattern types so that we can
         ; group all the types together that correspond to the same value. We also want to do the same
         ; for the patterns themselves, though only to provide useful source location information for
         ; type errors errors.
         (define tss_pats-transposed (apply map list tss_pats))
         (define patss-transposed (apply map list (attribute clause.pat)))]
   ; Now we can iterate over the types and ensure each value has the appropriate type.
   #:with [val- ...] (for/list ([val (in-list (attribute val))]
                                [ts_pats (in-list tss_pats-transposed)]
                                [pats (in-list patss-transposed)])
                       (let ([val^ (generate-temporary)])
                         (for-each #{type<:! %1 #`(#%type:wobbly-var #,val^) #:src %2} ts_pats pats)
                         (τ⇐! val (apply-current-subst #`(#%type:wobbly-var #,val^)))))

   #:do [; Perform exhaustiveness checking.
         (define non-exhaust (check-exhaustiveness (attribute clause.pat.pat)
                                                   (length (attribute val))))]
   #:fail-when non-exhaust
               (string-append "non-exhaustive pattern match\n  unmatched case"
                              (if (= (length non-exhaust) 1) "" "s")
                              ":" (string-append* (map #{string-append "\n    " (ideal->string %)}
                                                       non-exhaust)))

   #:do [; The resulting type of the case expression is the type we unified each clause against.
         (define t_result
           (apply-current-subst t_body))]

   ; Finally, we can actually emit the result syntax, using racket/match.
   #:with [match-pat- ...] match-pats-
   #:with [body- ...] bodies-
   (~> (syntax/loc this-syntax
         (lazy- (match*- [val- ...] [match-pat- body-] ...)))
       (attach-type t_result)
       (syntax-property 'disappeared-use (attribute clause.pat.disappeared-uses)))])

(define-syntax-parser case
  [(_ val:expr {~describe "a pattern-matching clause" [pat:pat body:expr]} ...+)
   (syntax/loc this-syntax
     (case* [val]
       [[pat] body] ...))])

(define-syntax-parser λ
  [(_ [pat:pat ...+] e:expr)
   (syntax/loc this-syntax
     (λ* [[pat ...] e]))])

(begin-for-syntax
  (define-splicing-syntax-class λ*-clauses
    #:description "a pattern-matching clause"
    #:attributes [[arg-id 1] [clause 1]]
    [pattern {~seq {~and clause [[pat:pat ...+] e:expr]} ...+}
             #:do [(define num-pats (length (first (attribute pat))))]
             #:fail-when (ormap #{and (not (= %1 num-pats)) %2}
                                (rest (map length (attribute pat)))
                                (rest (attribute clause)))
                         "all clauses must have the same number of patterns"
             #:with [arg-id ...] (map #{datum->syntax %1 (syntax-e %1) %2}
                                      (generate-temporaries (first (attribute pat)))
                                      (first (attribute pat)))]))

(define-syntax-parser λ*
  [(_ clauses:λ*-clauses)
   (quasisyntax/loc this-syntax
     (plain-λ [clauses.arg-id ...]
       #,(syntax/loc this-syntax
           (case* [clauses.arg-id ...]
             clauses.clause ...))))])

(define-syntax-parser defn
  #:literals [:]
  [(_ id:id
      {~or {~optional {~seq {~and : {~var :/use}} {~type t:type}}}
           {~optional fixity:fixity-annotation}}
      ...
      clauses:λ*-clauses)
   (quasitemplate
    (def id {?? {?@ :/use t}} {?? {?@ . fixity}}
      #,(syntax/loc this-syntax
          (λ* clauses.clause ...))))])
