#lang curly-fn racket/base

(require racket/require hackett/private/util/require)

(require (for-syntax (multi-in racket [base contract list match syntax])
                     syntax/parse/experimental/template
                     syntax/intdef
                     syntax/srcloc
                     threading)
         (postfix-in - (combine-in racket/base
                                   racket/promise))
         racket/stxparam
         syntax/parse/define

         (for-syntax hackett/private/expand+elaborate
                     hackett/private/infix
                     hackett/private/typecheck
                     hackett/private/typeclass
                     hackett/private/util/list
                     hackett/private/util/stx))

(provide (for-syntax (all-from-out hackett/private/typecheck)
                     (all-from-out hackett/private/typeclass)
                     τs⇔/λ! τ⇔/λ! τ⇔! τ⇐/λ! τ⇐! τ⇒/λ! τ⇒! τ⇒app! τs⇒!)
         (rename-out [#%top @%top])
         @%module-begin @%datum @%app
         @%superclasses-key @%dictionary-placeholder @%with-dictionary
         define-primop define-base-type
         -> Integer Double String Bytes
         core-def
         : λ1 def let letrec todo!)

(define-base-type Integer)
(define-base-type Double)
(define-base-type String)
(define-base-type Bytes)

(define-syntax-parser define-primop
  #:literals [:]
  [(_ op:id op-:id colon:: t:type)
   (~> #'(define-syntax op (make-typed-var-transformer #'op- (quote-syntax t.expansion)))
       (syntax-property 'disappeared-use (list (syntax-local-introduce #'op-)
                                               (syntax-local-introduce #'colon))))])

(begin-for-syntax
  ;; -------------------------------------------------------------------------------------------------
  ;; inference/checking + erasure/expansion

  ; The following functions perform type inference and typechecking. This process is performed by
  ; expanding expressions, which can also be seen as a type erasure pass. These functions follow a
  ; mnemonic naming convention, with the following letters and symbols having the following meaning:
  ;
  ;   τ    type
  ;   τs   types
  ;
  ;   ⇒    infer
  ;   ⇐    check
  ;   ⇔    infer & check
  ;
  ;   /λ   with bindings/assumptions
  ;   !    side-effectfully (mutating the type context)
  ;
  ; For example, τ⇒! means “infer a type, using the current type context”, and τs⇐/λ! means “check
  ; the types for multiple expressions, with a set of assumptions, using the current type context”.

  ; The most general function for checking or inferring types. This function allows many expressions
  ; to be checked or inferred with a single set of assumptions, which eliminates the proliferation of
  ; duplicate bindings that would otherwise occur when typechecking letrec. Other forms can get away
  ; with using the simpler τ⇒/λ! and τ⇐/λ! for inference and checking of a single expression,
  ; respectively.
  (define/contract (τs⇔/λ! es+ts bindings)
    (-> (listof (cons/c syntax? (or/c type? #f)))
        (listof (cons/c identifier? type?))
        (values (listof identifier?) (listof syntax?) (listof type?)))

    ; This helper function handles checking behavior after inference. It accepts an expression and
    ; possibly a type as input. If the provided type is actually a type (and isn’t #f), this function
    ; operates in checking mode, otherwise it operates in inference mode.
    ;
    ; The result of this function is a syntax object to serve as the expression (checking mode adds a
    ; property before handing the expression off for expansion), possibly an internal definition
    ; context to use when expanding the expression (checking mode adds some bindings to this context
    ; to implement scoped type variables) and a continuation that accepts the fully-expanded syntax as
    ; well as its inferred type, which will be invoked after the inference process is complete. When
    ; in checking mode, this continuation checks that the inferred type matches the expected one, and
    ; it performs dictionary elaboration. In inference mode, the type and expression are passed along
    ; unchanged.
    (define/contract (simplify/elaborate e t)
      (-> syntax? (or/c type? #f)
          (list/c syntax? (or/c internal-definition-context? #f)
                  (-> syntax? type? (values syntax? type?))))
      (cond
        [t
         (syntax-parse t
           #:context 'simplify/elaborate
           #:literal-sets [type-literals]
           [{~and t:type {~parse (~#%type:forall* [x ...] a) #'t.expansion}}
            ; If the expected type is qualified, we need to skolemize it before continuing with
            ; inference.
            #:with [x^ ...] (generate-temporaries (attribute x))
            #:with [rigid-x^ ...] #'[(#%type:rigid-var x^) ...]
            #:with a_skolemized (let ([skolem-subst (map cons (attribute x) (attribute rigid-x^))])
                                  (insts #'a skolem-subst))
            ; To support scoped type variables, we want the same skolems to be in scope while
            ; expanding the expression.
            #:do [(define intdef-ctx (syntax-local-make-definition-context))
                  (syntax-local-bind-syntaxes (attribute x)
                                              #'(values (make-variable-like-transformer
                                                         (quote-syntax rigid-x^)) ...)
                                              intdef-ctx)]
            ; If the expected type is qualified, we need to wrap the expansion in the necessary set of
            ; @%with-dictionary forms to allow recieving the necessary typeclass dictionaries.
            #:with (~#%type:qual* [constr ...] b) #'a_skolemized
            (list
             (attach-expected ((attribute t.scoped-binding-introducer) e) #'b)
             intdef-ctx
             (λ (e- t_⇒)
               ; Once inference is finished, we first check that the inferred type matches the
               ; expected one. If so, it may have some extra constraints on it that need to be
               ; supplied dictionaries, so elaborate them here.
               (define e-elaborated
                 (let ([constrs (type<:/elaborate! t_⇒ #'b #:src e)])
                   (foldr #{quasisyntax/loc e
                             (lazy- (#%app- (force- #,%2)
                                            #,(quasisyntax/loc e
                                                (@%dictionary-placeholder #,%1 #,e))))}
                          e- constrs)))
               ; Next, we need to insert the necessary uses of @%with-dictionary, as described above.
               (define e-wrapped
                 (foldr #{quasisyntax/loc e
                           (@%with-dictionary #,%1 #,%2)}
                        e-elaborated (attribute constr)))
               ; Finally, include information about scoped type variable bindings for Check Syntax.
               (define e+disappeared-bindings
                 (internal-definition-context-track intdef-ctx e-wrapped))
               (values e+disappeared-bindings this-syntax)))])]
        [else
         ; If t is #f, we’re in inference mode, so we don’t need to do anything but pass values
         ; through unchanged.
         (list e #f (λ (e- t_⇒) (values e- t_⇒)))]))

    ; To begin the actual inference process, we need to generate some bindings for the assumptions. We
    ; do this by binding a slot for each identifier in a definition context, then binding each
    ; identifier to a typed variable transformer that expands to the generated slots. This code just
    ; binds the names of those bindings and their types.
    (define xs (map car bindings))
    (define xs- (generate-temporaries xs))
    (define ts_xs (map cdr bindings))

    ; Next, we need to call simplify/elaborate on each e+t pair we are provided. We bind the
    ; elaborated expressions and internal definition contexts to variables to be used in expansion,
    ; and we keep the continuations for later.
    (match-define (list (list es/elab scoped-intdef-ctxs ks) ...)
      (map #{simplify/elaborate (car %) (cdr %)} es+ts))

    ; Next, we need to expand each expression. We start by building an internal definition context,
    ; then binding the slots for the assumptions inside it.
    (define intdef-ctx (syntax-local-make-definition-context))
    (syntax-local-bind-syntaxes xs- #f intdef-ctx)
    ; We add the internal definition context’s scope to each temporary identifier to allow them to be
    ; used in reference and binding positions. We’ll need to return these at the end, to allow callers
    ; to arrange for these identifiers to appear in binding positions.
    (define xs-* (for/list ([x (in-list xs)]
                            [x- (in-list xs-)]
                            [t_x (in-list ts_xs)])
                   (attach-type (internal-definition-context-introduce intdef-ctx x-) t_x
                                #:tooltip-src x)))
    (for ([x (in-list xs)]
          [x-* (in-list xs-*)]
          [t_x (in-list ts_xs)])
      ; As previously mentioned, each assumption is bound to a typed variable transformer that expands
      ; to its temporary slot.
      (syntax-local-bind-syntaxes
       (list x)
       #`(make-typed-var-transformer (quote-syntax #,x-*) (quote-syntax #,t_x))
       intdef-ctx))

    ; With the internal definition context properly set up, we can actually perform expansion. We need
    ; to get the types attached to the expanded expressions and call the continuations produced by
    ; simplify/elaborate from earlier. This will produce a fully-expanded expression and its type,
    ; which we can return.
    (define-values [es- ts_es]
      ; In order to ensure Check Syntax can pick up uses of typed var transformers that have been
      ; expanded, it’s important to attach the necessary 'disappeared-binding syntax property.
      (let ([disappeared-bindings (map (λ~>> (internal-definition-context-introduce intdef-ctx)
                                             syntax-local-introduce)
                                       xs)])
        (for/lists [es- ts_es]
                   ([k (in-list ks)]
                    [e (in-list (map car es+ts))]
                    [e/elab (in-list es/elab)]
                    [scoped-intdef-ctx (in-list scoped-intdef-ctxs)])
          (let* ([e- (let ([intdef-ctxs (if scoped-intdef-ctx
                                            (list intdef-ctx scoped-intdef-ctx)
                                            (list intdef-ctx))])
                       (let loop ([e e/elab])
                         (syntax-parse (local-expand/defer-elaborate e 'expression '() intdef-ctxs)
                           #:literals [#%expression]
                           ; Expand through #%expression forms if we don’t find an inferred type
                           ; immediately and hope that the nested expression will have a type.
                           [(head:#%expression e*)
                            #:when (not (get-type this-syntax))
                            (syntax-track-origin (loop #'e*) this-syntax #'head)]
                           ; If we find a bare identifier, it’s either a variable, an out-of-context
                           ; identifier, or an unbound identifier that stopped expanding just before
                           ; introducing racket/base’s #%top (since that #%top is implicitly added to
                           ; the stop list). The former two cases are okay, but the latter is not, so
                           ; keep going to trigger the unbound identifier error if the identifier is
                           ; actually unbound.
                           [_:id
                            #:when (not (identifier-binding this-syntax))
                            (local-expand this-syntax 'expression '() intdef-ctxs)]
                           [_ this-syntax])))]
                 [t_e (get-type e-)])
            (unless t_e (raise-syntax-error #f "no inferred type" e-))
            (k (syntax-property e- 'disappeared-binding
                                (cons (syntax-property e 'disappeared-binding) disappeared-bindings))
               t_e)))))

    ; With everything inferred and checked, all that’s left to do is return the results.
    (values xs-* es- ts_es))

  (define/contract (τ⇔/λ! e t bindings)
    (-> syntax? (or/c type? #f) (listof (cons/c identifier? type?))
        (values (listof identifier?) syntax? type?))
    (match-let-values ([(xs- (list e-) (list t_e)) (τs⇔/λ! (list (cons e t)) bindings)])
      (values xs- e- t_e)))

  (define/contract (τ⇒/λ! e bindings)
    (-> syntax? (listof (cons/c identifier? type?)) (values (listof identifier?) syntax? type?))
    (τ⇔/λ! e #f bindings))

  (define/contract (τ⇐/λ! e t bindings)
    (-> syntax? type? (listof (cons/c identifier? type?)) (values (listof identifier?) syntax?))
    (match-let-values ([(xs- e- _) (τ⇔/λ! e t bindings)])
      (values xs- e-)))

  (define/contract (τ⇔! e t)
    (-> syntax? (or/c type? #f) (values syntax? type?))
    (match-let-values ([(_ e- t_e) (τ⇔/λ! e t '())])
      (values e- t_e)))

  (define/contract (τ⇒! e)
    (-> syntax? (values syntax? type?))
    (τ⇔! e #f))

  (define/contract (τ⇐! e t)
    (-> syntax? type? syntax?)
    (match-let-values ([(e- _) (τ⇔! e t)])
      e-))

  (define/contract (τ⇒app! e_fn t_fn e_arg #:src src)
    (-> syntax? type? syntax? #:src syntax? (values syntax? type?))
    (syntax-parse t_fn
      #:context 'τ⇒app!
      #:literal-sets [type-literals]
      [(#%type:wobbly-var x^)
       #:with [x1^ x2^] (generate-temporaries #'[x^ x^])
       (type-inst-l! #'x^ (template (?->* (#%type:wobbly-var x1^) (#%type:wobbly-var x2^))))
       (values (quasisyntax/loc src
                 (lazy- (#%app- (force- #,e_fn) #,(τ⇐! e_arg #'(#%type:wobbly-var x1^)))))
               #'(#%type:wobbly-var x2^))]
      [(~-> a b)
       (values (quasisyntax/loc src
                 (lazy- (#%app- (force- #,e_fn) #,(τ⇐! e_arg #'a))))
               #'b)]
      [(#%type:forall x t)
       #:with x^ (generate-temporary #'x)
       (τ⇒app! e_fn (inst #'t #'x #'(#%type:wobbly-var x^)) e_arg #:src src)]
      [(#%type:qual constr t)
       (τ⇒app! (quasisyntax/loc src
                 (lazy- (#%app- (force- #,e_fn)
                                #,(quasisyntax/loc src
                                    (@%dictionary-placeholder constr #,src)))))
               #'t e_arg #:src src)]
      [_ (raise-syntax-error #f (format "cannot apply expression of type ~a to expression ~a"
                                        (type->string t_fn) (syntax->datum e_arg))
                             e_arg)]))

  (define/contract (τs⇒! es)
    (-> (listof syntax?) (values (listof syntax?) (listof type?)))
    (for/fold ([es- '()]
               [ts '()])
              ([e (in-list es)])
      (let-values ([(e- t) (τ⇒! e)])
        (values (snoc es- e-) (snoc ts t))))))

(define-syntax-parser @%with-dictionary
  [(_ constr e)
   #:with dict-id (generate-temporary #'constr)
   (syntax/loc this-syntax
     (@%with-dictionary* constr dict-id e))])

(define-syntax-parser @%with-dictionary*
  [(head constr dict-id:id e)
   #:fail-unless (syntax-local-elaborate-pass) "not currently elaborating"
   (match (syntax-local-elaborate-pass)
     ['expand
      (syntax-local-elaborate-defer
       (quasisyntax/loc this-syntax
         (head constr dict-id #,(local-expand/defer-elaborate #'e 'expression '()))))]
     ['elaborate
      (let* ([intdef-ctx (syntax-local-make-definition-context)]
             [dict-id* (internal-definition-context-introduce intdef-ctx #'dict-id)]
             [new-instances (constr->instances #'constr dict-id*)])
        (syntax-local-bind-syntaxes (list #'dict-id) #f intdef-ctx)
        (parameterize ([current-local-class-instances
                        (append new-instances (current-local-class-instances))])
          (syntax-local-elaborate-defer
           (quasisyntax/loc this-syntax
             (head constr #,dict-id*
                   #,(local-expand/defer-elaborate #'e 'expression '() (list intdef-ctx)))))))]
     ['finalize
      (let ([new-instances (constr->instances #'constr #'dict-id)])
        (parameterize ([current-local-class-instances
                        (append new-instances (current-local-class-instances))])
          (local-expand/defer-elaborate
           (syntax/loc this-syntax
             (λ- (dict-id) e))
           'expression '())))])])

(define-syntax @%dictionary-placeholder
  (make-elaborating-transformer
   (syntax-parser
     [(_ constr src-expr)
      (match (syntax-local-elaborate-pass)
        ['expand
         (syntax-local-elaborate-defer this-syntax)]
        [(or 'elaborate 'finalize)
         (let*-values ([(instance constrs)
                        (lookup-instance!
                         #'constr
                         #:src #'src-expr
                         #:failure-thunk (and (eq? (syntax-local-elaborate-pass) 'elaborate)
                                              (λ () (values #f #f))))])
           (if instance
               ; It’s possible that the dictionary itself requires dictionaries for classes with
               ; subgoals, like (instance ∀ [a] [(Show a)] => (Show (List a)) ...). If there are not
               ; any constraints, we need to produce a (curried) application to sub-dictionaries,
               ; which should be recursively elaborated.
               (begin
                 (syntax-local-elaborate-did-make-progress!)
                 (foldr (λ (constr acc)
                          #`(#,acc
                             #,(quasisyntax/loc this-syntax
                                 (@%dictionary-placeholder #,constr src-expr))))
                        (replace-stx-loc (class:instance-dict-expr instance) this-syntax)
                        constrs))
               (syntax-local-elaborate-defer this-syntax #:did-defer!? #t)))])])))

;; ---------------------------------------------------------------------------------------------------

(define-syntax-parser @%module-begin
  [(_ form ...)
   (~> (syntax/loc this-syntax
         (#%plain-module-begin- form ...))
       value-namespace-introduce
       local-expand+elaborate
       apply-current-subst-in-tooltips)])

(define-syntax-parser @%datum
  [(_ . n:exact-integer)
   (attach-type #'(#%datum . n) (expand-type #'Integer) #:tooltip-src #'n)]
  [(_ . n:number)
   #:when (double-flonum? (syntax-e #'n))
   (attach-type #'(#%datum . n) (expand-type #'Double) #:tooltip-src #'n)]
  [(_ . s:string)
   (attach-type #'(#%datum . s) (expand-type #'String) #:tooltip-src #'s)]
  [(_ . b:bytes)
   (attach-type #'(#%datum . b) (expand-type #'Bytes) #:tooltip-src #'b)]
  [(_ . x)
   (raise-syntax-error #f "literal not supported" #'x)])

(define-syntax :
  (make-trampolining-expression-transformer
   (syntax-parser
     ; The #:exact option prevents : from performing context reduction. This is not normally
     ; important, but it is required for forms that use : to ensure an expression has a particular
     ; shape in order to interface with untyped (i.e. Racket) code, and therefore the resulting type
     ; is ignored. For example, the def form wraps an expression in its expansion with :, but it binds
     ; the actual identifier to a syntax transformer that attaches the type directly. Therefore, it
     ; needs to perform context reduction itself prior to expanding to :, and it must use #:exact.
     [(_ e {~type t:type} {~optional {~and #:exact exact?}})
      #:with t_reduced (if (attribute exact?)
                           #'t.expansion
                           (type-reduce-context #'t.expansion))
      (attach-type #`(let-values- ([() t.residual])
                                  #,(τ⇐! ((attribute t.scoped-binding-introducer) #'e) #'t_reduced))
                   #'t_reduced)])))

(define-syntax λ1
  (make-trampolining-expression-transformer
   (syntax-parser
     [(_ x:id e:expr)
      #:do [(define t (get-expected this-syntax))]
      #:fail-unless t "no expected type, add more type annotations"
      #:with {~or {~-> a b} {~fail (format "expected ~a, given function" (type->string t))}} t
      #:do [(define-values [xs- e-] (τ⇐/λ! #'e #'b (list (cons #'x #'a))))]
      #:with [x-] xs-
      (attach-type #`(λ- (x-) #,e-) t)]
     [(_ x:id e:expr)
      #:with x^ (generate-temporary)
      #:with y^ (generate-temporary)
      #:do [(define-values [xs- e-]
              (τ⇐/λ! #'e #'(#%type:wobbly-var y^) (list (cons #'x #'(#%type:wobbly-var x^)))))]
      #:with [x-] xs-
      (attach-type #`(λ- (x-) #,e-)
                   (template (?->* (#%type:wobbly-var x^) (#%type:wobbly-var y^))))])))

(define-syntax @%app
  (make-trampolining-expression-transformer
   (syntax-parser
     [(_ f:expr e:expr)
      #:do [(define-values [f- t_f] (τ⇒! #'f))
            (define-values [r- t_r] (τ⇒app! f- (apply-current-subst t_f) #'e
                                            #:src this-syntax))]
      (attach-type r- t_r #:tooltip-src this-syntax)])))

;; core-def is an annotated definition
;; a `def` expands to `core-def` to define a typed variable
(define-syntax-parser core-def
  #:literals [:]
  [(_ id:id id-:id
      {~alt {~once {~seq {~and : {~var :/use}} {~type t:type}
                         {~optional {~and #:exact exact?}}}}
            {~optional fixity:fixity-annotation}}
      ...
      e:expr)
   #:with t_reduced (if (attribute exact?) #'t.expansion (type-reduce-context #'t.expansion))
   #`(begin-
       #,(indirect-infix-definition
          #'(define-syntax- id (make-typed-var-transformer #'id- (quote-syntax t_reduced)))
          (attribute fixity.fixity))
       (define- id- (:/use #,((attribute t.scoped-binding-introducer) #'e) t_reduced #:exact)))])

(define-syntax-parser def
  #:literals [:]
  [(_ id:id
      {~and
       {~seq stuff ...}
       {~seq
        {~or {~once {~seq {~and : {~var :/use}} {~type t:type}
                          {~optional {~and #:exact exact?}}}}
             {~optional fixity:fixity-annotation}}
        ...
        e:expr}})
   #:with id- (generate-temporary #'id)
   #'(core-def id id- stuff ...)]
  [(_ id:id
      {~and {~seq fixity-stuff ...}
            {~optional fixity:fixity-annotation}}
      e:expr)
   (if (and (eq? (syntax-local-context) 'top-level)
            (not (syntax-local-elaborate-pass)))
       (syntax-local-elaborate-top this-syntax)
       (match-let*-values ([[t_e] #`(#%type:wobbly-var #,(generate-temporary))]
                           [[(list id-) e-] (τ⇐/λ! #'e t_e (list (cons #'id t_e)))]
                           [[t_gen] (type-reduce-context (generalize (apply-current-subst t_e)))])
         #`(core-def id #,id- : #,t_gen #:exact fixity-stuff ...
             #,e-)))])

(begin-for-syntax
  (struct todo-item (full summary) #:prefab))

(define-syntax todo!*
  (make-elaborating-transformer
   (syntax-parser
     [(_ v e ...)
      (match (syntax-local-elaborate-pass)
        [(or 'expand 'elaborate)
         (syntax-local-elaborate-defer this-syntax)]
        ['finalize
         (let* ([type-str (type->string (apply-current-subst #'(#%type:wobbly-var v)))]
                [message (string-append (source-location->prefix this-syntax)
                                        "todo! with type "
                                        type-str)])
           (syntax-property (quasisyntax/loc this-syntax (error '#,message))
                            'todo (todo-item type-str type-str)))])])))

(define-syntax todo!
  (make-elaborating-transformer
   #:allowed-passes '[expand]
   (syntax-parser
     [(_ e ...)
      #:with var (generate-temporary #'t_todo!)
      (attach-type (syntax-local-elaborate-defer (syntax/loc this-syntax (todo!* var e ...)))
                   #'(#%type:wobbly-var var))])))

(define-syntax let1
  (make-trampolining-expression-transformer
   (syntax-parser
     #:literals [:]
     [(_ [id:id {~optional {~seq colon:: {~type t-ann:type}}} val:expr] body:expr)
      #:do [(define-values [val- t_val]
              (τ⇔! #'val (and~> (attribute t-ann.expansion) type-reduce-context)))
            (match-define-values [(list id-) body- t_body]
              (τ⇔/λ! #'body (get-expected this-syntax) (list (cons #'id t_val))))]
      (~> (quasitemplate/loc this-syntax
                             (let-values- ([(#,id-) #,val-]
                                           {?? [() t-ann.residual]})
                                          #,body-))
          (attach-type t_body)
          (syntax-property 'disappeared-use (and~> (attribute colon) syntax-local-introduce)))])))

(define-syntax-parser let
  #:literals [:]
  [(_ ([id:id {~optional {~seq colon:: {~type t-ann:type}}} val:expr] ...+) body:expr)
   (syntax-parse this-syntax
     [(_ (binding-pair) body)
      (syntax/loc this-syntax
        (let1 binding-pair body))]
     [(_ (binding-pair binding-pairs ...+) body)
      (quasisyntax/loc this-syntax
        (let1 binding-pair
          #,(syntax/loc this-syntax
              (let (binding-pairs ...) body))))])])

(define-syntax letrec
  (make-trampolining-expression-transformer
   (syntax-parser
     #:literals [:]
     [(_ ([id:id {~optional {~seq colon:: {~type t-ann:type}}} val:expr] ...+) body:expr)
      #:do [; First, start by grouping bindings into two sets: those with explicit type annotations,
            ; and those without. For those without explicit type annotations, synthesize a fresh type
            ; variable to serve as their types.
            (define-values [ids+ts+vals/ann ids+ts+vals/unann]
              (let-values
                  ([(ids+ts+vals/ann ids+ts+vals/unann)
                    (for/fold ([ids+ts+vals/ann '()]
                               [ids+ts+vals/unann '()])
                              ([id (in-list (attribute id))]
                               [t-ann (in-list (attribute t-ann.expansion))]
                               [val (in-list (attribute val))])
                      (if t-ann
                          (values (cons (list id (type-reduce-context t-ann) val)
                                        ids+ts+vals/ann)
                                  ids+ts+vals/unann)
                          (let* ([t_val-id (generate-temporary)]
                                 [t_val #`(#%type:wobbly-var #,t_val-id)])
                            (values ids+ts+vals/ann (cons (list id t_val val) ids+ts+vals/unann)))))])
                (values (reverse ids+ts+vals/ann) (reverse ids+ts+vals/unann))))

            ; Next, establish a dictionary mapping all bindings to their types. This will be used as a
            ; binding context when typechecking.
            (define ids+ts (map #{cons (first %) (second %)}
                                (append ids+ts+vals/ann ids+ts+vals/unann)))
            ; We also need to produce a mapping of expressions to their annotations, plus the body.
            ; This will be handed off to the expander to be typechecked.
            (define es+ts
              (snoc (map #{cons (third %) (second %)} (append ids+ts+vals/ann ids+ts+vals/unann))
                    (cons #'body (get-expected this-syntax))))

            ; With the setup out of the way, we can now call τs⇔/λ! to perform the actual
            ; typechecking.
            (match-define-values [ids- (list vals- ... body-) (list _ ... t_body)]
              (τs⇔/λ! es+ts ids+ts))]

      ; Finally, expand to the runtime value.
      #:with [id- ...] ids-
      #:with [val- ...] vals-
      (~> (quasitemplate/loc this-syntax
                             (letrec-values ([(id-) val-] ...
                                             {?? [() t-ann.residual]} ...)
                               #,body-))
          (attach-type t_body)
          (syntax-property 'disappeared-use
                           (map syntax-local-introduce (filter values (attribute colon)))))])))
