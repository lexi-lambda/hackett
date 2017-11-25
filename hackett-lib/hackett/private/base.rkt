#lang curly-fn racket/base

(require racket/provide racket/require hackett/private/util/require)

(require (for-syntax (multi-in racket [base contract list match provide-transform require-transform
                                       syntax])
                     syntax/parse/experimental/template
                     threading)
         (postfix-in - (combine-in racket/base
                                   racket/promise
                                   syntax/id-table))
         racket/stxparam
         syntax/parse/define

         (for-syntax hackett/private/infix
                     hackett/private/typecheck
                     hackett/private/util/list
                     hackett/private/util/stx))

(provide (for-syntax (all-from-out hackett/private/typecheck)
                     τs⇔/λ! τ⇔/λ! τ⇔! τ⇐/λ! τ⇐! τ⇒/λ! τ⇒! τ⇒app! τs⇒!)
         (rename-out [#%top @%top]
                     [∀ forall])
         @%module-begin @%datum @%app @%superclasses-key @%dictionary-placeholder @%with-dictionary
         define-primop define-base-type
         -> ∀ => Integer Double String
         : λ1 def let letrec)

(define-simple-macro (define-base-type name:id)
  (define-syntax name (make-type-variable-transformer (τ:con #'name #f))))

(define-base-type Integer)
(define-base-type Double)
(define-base-type String)

(define-syntax-parser define-primop
  #:literals [:]
  [(_ op:id op-:id colon:: t-expr:type)
   #:with t (preservable-property->expression (attribute t-expr.τ))
   (~> #'(begin-
           (define-values- [] (begin- (λ- () t-expr.expansion) (values-)))
           (define-syntax op (make-typed-var-transformer #'op- t)))
       (syntax-property 'disappeared-use (list (syntax-local-introduce #'op-)
                                               (syntax-local-introduce #'colon))))])

(define-syntax ->/prefix (make-type-variable-transformer τ:->))
(define-syntax -> (infix-operator-impl #'->/prefix 'right))

(define-syntax-parser ∀
  #:literals [let-values]
  [(_ x:id t)
   #:with x- (generate-temporary #'x)
   #:with x/τ (preservable-property->expression (τ:var #'x-))
   #:with (let-values _ {~and inner-let (let-values _ t-:type)})
          (local-expand-type #'(let-syntax ([x (make-type-variable-transformer x/τ)])
                                 t))
   (~> (τ-stx-token (τ:∀ #'x- (attribute t-.τ))
                    #:expansion #'(void- t-.expansion))
       (syntax-property 'disappeared-binding (syntax-property #'inner-let 'disappeared-binding)))])

(define-syntax-parser =>
  [(_ constr:type t:type)
   (τ-stx-token (τ:qual (attribute constr.τ) (attribute t.τ))
                #:expansion #'(void- constr.expansion t.expansion))])

(define-syntax (@%superclasses-key stx)
  (raise-syntax-error #f "cannot be used as an expression" stx))

(begin-for-syntax
  ;; -------------------------------------------------------------------------------------------------
  ;; inference/checking + erasure/expansion

  (define stop-ids (list #'@%dictionary-placeholder #'@%with-dictionary))

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
    (-> (listof (cons/c syntax? (or/c τ? #f)))
        (listof (cons/c identifier? τ?))
        (values (listof identifier?) (listof syntax?) (listof τ?)))

    ; This helper function handles checking behavior after inference. It accepts an expression and
    ; possibly a type as input. If the provided type is actually a type (and isn’t #f), this function
    ; operates in checking mode, otherwise it operates in inference mode.
    ;
    ; The result of this function is a syntax object to serve as the expression (checking mode adds a
    ; property before handing the expression off for expansion) and a continuation that accepts the
    ; fully-expanded syntax as well as its inferred type, which will be invoked after the inference
    ; process is complete. When in checking mode, this continuation checks that the inferred type
    ; matches the expected one, and it performs dictionary elaboration. In inference mode, the type
    ; and expression are passed along unchanged.
    (define/contract (simplify/elaborate e t)
      (-> syntax? (or/c τ? #f)
          (list/c syntax? (-> syntax? τ? (values syntax? τ?))))
      (when t
        (current-τ-wf! t))
      (match t
        ; If t is #f, we’re in inference mode, so we don’t need to do anything but pass values through
        ; unchanged.
        [#f
         (list e (λ (e- t_⇒) (values e- t_⇒)))]
        ; If the expected type is quantified, we need to skolemize it before continuing with
        ; inference.
        [(τ:∀ x a)
         (let ([x^ (generate-temporary x)])
           (modify-type-context #{snoc % (ctx:skolem x^)})
           (match-let ([(list e* k) (simplify/elaborate e (inst a x (τ:skolem x^)))])
             (list e* (λ (e- t_⇒)
                        (begin0
                          (k e- t_⇒)
                          (modify-type-context #{ctx-remove % (ctx:skolem x^)}))))))]
        ; If the expected type is qualified, we need to wrap the expression with a lambda so that it
        ; can receive a dictionary.
        [(τ:qual constr a)
         (match-let ([(list e* k) (simplify/elaborate e a)])
           (list e* (λ (e- t_⇒)
                      (let-values ([(e-* t*) (k e- t_⇒)])
                        (values
                         (quasisyntax/loc e-*
                           (@%with-dictionary #,(preservable-property->expression constr) #,e-*))
                         t*)))))]
        ; Otherwise, we are in checking mode with no special cases. We need to infer and expand, then
        ; check that the types match and elaborate dictionaries.
        [_
         (list (attach-expected e t)
               (λ (e- t_⇒)
                 (let ([constrs (τ<:/elaborate! t_⇒ t #:src e)])
                   (values (foldr #{begin (quasisyntax/loc e
                                            (lazy- (#%app- (force- #,%2)
                                                           #,(quasisyntax/loc e
                                                               (@%dictionary-placeholder
                                                                #,(preservable-property->expression
                                                                   %1)
                                                                #,e)))))}
                                  e- constrs)
                           t))))]))

    ; To begin the actual inference process, we need to generate some bindings for the assumptions. We
    ; do this by binding a slot for each identifier in a definition context, then binding each
    ; identifier to a typed variable transformer that expands to the generated slots. This code just
    ; binds the names of those bindings and their types.
    (define xs (map car bindings))
    (define xs- (generate-temporaries xs))
    (define ts_xs (map (λ~> cdr preservable-property->expression) bindings))
    
    ; Next, we need to call simplify/elaborate on each e+t pair we are provided. We bind the
    ; elaborated expressions to a variable to be used in expansion, and we keep the continuations for
    ; later.
    (match-define (list (list es/elab ks) ...) (map #{simplify/elaborate (car %) (cdr %)} es+ts))

    ; Next, we need to expand each expression. We start by building an internal definition context,
    ; then binding the slots for the assumptions inside it.
    (define intdef-ctx (syntax-local-make-definition-context))
    (syntax-local-bind-syntaxes xs- #f intdef-ctx)
    ; We add the internal definition context’s scope to each temporary identifier to allow them to be
    ; used in reference and binding positions. We’ll need to return these at the end, to allow callers
    ; to arrange for these identifiers to appear in binding positions.
    (define xs-* (map #{internal-definition-context-introduce intdef-ctx %} xs-))
    (for ([x (in-list xs)]
          [x-* (in-list xs-*)]
          [t_x (in-list ts_xs)])
      ; As previously mentioned, each assumption is bound to a typed variable transformer that expands
      ; to its temporary slot.
      (syntax-local-bind-syntaxes
       (list x)
       #`(make-typed-var-transformer (quote-syntax #,x-*) #,t_x)
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
                  [e/elab (in-list es/elab)])
        (let* ([e- (local-expand e/elab 'expression stop-ids intdef-ctx)]
               [t_e (get-type e-)])
          (unless t_e (raise-syntax-error #f "no inferred type" e))
          (k (syntax-property e- 'disappeared-binding
                              (cons (syntax-property e 'disappeared-binding) disappeared-bindings))
             t_e)))))

    ; With everything inferred and checked, all that’s left to do is return the results.
    (values xs-* es- ts_es))

  (define/contract (τ⇔/λ! e t bindings)
    (-> syntax? (or/c τ? #f) (listof (cons/c identifier? τ?))
        (values (listof identifier?) syntax? τ?))
    (match-let-values ([(xs- (list e-) (list t_e)) (τs⇔/λ! (list (cons e t)) bindings)])
      (values xs- e- t_e)))

  (define/contract (τ⇒/λ! e bindings)
    (-> syntax? (listof (cons/c identifier? τ?)) (values (listof identifier?) syntax? τ?))
    (τ⇔/λ! e #f bindings))

  (define/contract (τ⇐/λ! e t bindings)
    (-> syntax? τ? (listof (cons/c identifier? τ?)) (values (listof identifier?) syntax?))
    (match-let-values ([(xs- e- _) (τ⇔/λ! e t bindings)])
      (values xs- e-)))

  (define/contract (τ⇔! e t)
    (-> syntax? (or/c τ? #f) (values syntax? τ?))
    (match-let-values ([(_ e- t_e) (τ⇔/λ! e t '())])
      (values e- t_e)))

  (define/contract (τ⇒! e)
    (-> syntax? (values syntax? τ?))
    (τ⇔! e #f))

  (define/contract (τ⇐! e t)
    (-> syntax? τ? syntax?)
    (match-let-values ([(e- _) (τ⇔! e t)])
      e-))

  (define/contract (τ⇒app! e_fn t_fn e_arg #:src src)
    (-> syntax? τ? syntax? #:src syntax? (values syntax? τ?))
    (match t_fn
      [(τ:var^ x^)
       (let ([x1^ (generate-temporary x^)]
             [x2^ (generate-temporary x^)])
         (modify-type-context #{snoc % (ctx:solution x^ (τ:->* (τ:var^ x1^) (τ:var^ x2^)))})
         (values (quasisyntax/loc src
                   (lazy- (#%app- (force- #,e_fn) #,(τ⇐! e_arg (τ:var^ x1^)))))
                 (τ:var^ x2^)))]
      [(τ:->* a b)
       (values (quasisyntax/loc src
                 (lazy- (#%app- (force- #,e_fn) #,(τ⇐! e_arg a))))
               b)]
      [(τ:∀ x t)
       (let ([x^ (generate-temporary x)])
         (τ⇒app! e_fn (inst t x (τ:var^ x^)) e_arg #:src src))]
      [(τ:qual constr t)
       (τ⇒app! (quasisyntax/loc src
                 (lazy- (#%app- (force- #,e_fn)
                                #,(quasisyntax/loc src
                                    (@%dictionary-placeholder
                                     #,(preservable-property->expression constr)
                                     #,src)))))
               t e_arg #:src src)]
      [_ (raise-syntax-error #f (format "cannot apply expression of type ~a to expression ~a"
                                        (τ->string t_fn) (syntax->datum e_arg))
                             e_arg)]))

  (define/contract (τs⇒! es)
    (-> (listof syntax?) (values (listof syntax?) (listof τ?)))
    (for/fold ([es- '()]
               [ts '()])
              ([e (in-list es)])
      (let-values ([(e- t) (τ⇒! e)])
        (values (snoc es- e-) (snoc ts t)))))

  ; Given a constraint, calculate the instances it brings in scope, including instances that can be
  ; derived via superclasses. For example, the constraint (Monad m) brings in three instances, one for
  ; Monad and two for Functor and Applicative.
  (define/contract constraint->instances
    (-> constr? syntax? (listof class:instance?))
    (match-lambda**
     [[(τ:app* (τ:con class-id _) ts ...) dict-expr]
      (let* ([class-info (syntax-local-value class-id)]
             [instance (class:instance class-info '() '() (map apply-current-subst ts) dict-expr)]
             ; instantiate the superclass constraints, so for (Monad Unit), we get (Applicative Unit)
             ; instead of (Applicative m)
             [super-constrs (~>> (class:info-superclasses class-info)
                                 (map #{insts % (map cons (class:info-vars class-info) ts)}))]
             [superclass-dict-expr #`(free-id-table-ref- #,dict-expr #'@%superclasses-key)]
             [super-instances (for/list ([(super-constr i) (in-indexed (in-list super-constrs))])
                                (constraint->instances
                                 super-constr
                                 #`(vector-ref- #,superclass-dict-expr '#,i)))])
        (cons instance (append* super-instances)))])))

(define-syntax-parser @%with-dictionary
  [(_ constr-expr e)
   #:with this #`(quote-syntax #,this-syntax)
   #:with dict-id (generate-temporary #'constr-expr)
   #'(λ- (dict-id)
       (syntax-parameterize
           ([local-class-instances
             (let ([existing-instances (syntax-parameter-value #'local-class-instances)]
                   [new-instances (constraint->instances constr-expr #'dict-id)])
               (append new-instances existing-instances))])
         e))])

(define-syntax-parser @%dictionary-placeholder
  [(_ constr-expr src-expr)
   #:with this #`(quote-syntax #,this-syntax)
   #'(let-syntax-
         ([dict-expr
           (let*-values ([(constr) constr-expr]
                         [(instance constrs) (lookup-instance! constr #:src (quote-syntax src-expr))]
                         [(dict-expr) (class:instance-dict-expr instance)])
             ; It’s possible that the dictionary itself requires dictionaries for classes with
             ; subgoals, like (instance ∀ [a] [(Show a)] => (Show (List a)) ...). If there are not
             ; any constraints, we need to produce a (curried) application to sub-dictionaries, which
             ; should be recursively elaborated.
             (make-variable-like-transformer
              (foldr (λ (constr acc)
                       #`(#,acc
                          #,(quasisyntax/loc this
                              (@%dictionary-placeholder
                               #,(preservable-property->expression constr)
                               src-expr))))
                     dict-expr
                     constrs)))])
       dict-expr)])

;; ---------------------------------------------------------------------------------------------------

(define-syntax-parser @%module-begin
  [(_ form ...)
   (value-namespace-introduce
    (syntax/loc this-syntax
      (#%plain-module-begin- form ...)))])

(define-syntax-parser @%datum
  [(_ . n:exact-integer)
   (attach-type #'(#%datum . n) (parse-type #'Integer))]
  [(_ . n:number)
   #:when (double-flonum? (syntax-e #'n))
   (attach-type #'(#%datum . n) (parse-type #'Double))]
  [(_ . s:str)
   (attach-type #'(#%datum . s) (parse-type #'String))]
  [(_ . x)
   (raise-syntax-error #f "literal not supported" #'x)])

(define-syntax-parser :
  [(_ e {~type t-expr:type})
   (attach-type #`(let-values- ([() (begin- (λ- () t-expr.expansion) (values-))])
                    #,(τ⇐! #'e (attribute t-expr.τ)))
                (apply-current-subst (attribute t-expr.τ)))])

(define-syntax-parser λ1
  [(_ x:id e:expr)
   #:do [(define t (get-expected this-syntax))]
   #:fail-unless t "no expected type, add more type annotations"
   #:fail-unless (τ:->? t) (format "expected ~a, given function" (τ->string t))
   #:do [(match-define (τ:->* a b) t)
         (define-values [xs- e-] (τ⇐/λ! #'e b (list (cons #'x a))))]
   #:with [x-] xs-
   (attach-type #`(λ- (x-) #,e-) t)]
  [(_ x:id e:expr)
   #:do [(define x^ (generate-temporary))
         (define y^ (generate-temporary))
         (define-values [xs- e-] (τ⇐/λ! #'e (τ:var^ y^) (list (cons #'x (τ:var^ x^)))))]
   #:with [x-] xs-
   (attach-type #`(λ- (x-) #,e-) (τ:->* (τ:var^ x^) (τ:var^ y^)))])

(define-syntax (@%app stx)
  (if (type-transforming?)
      (syntax-parse stx
        [(_ a:type b:type)
         (τ-stx-token (τ:app (attribute a.τ) (attribute b.τ))
                      #:expansion #'(void- a.expansion b.expansion))])
      (syntax-parse stx
        [(_ f:expr e:expr)
         #:do [(define-values [f- t_f] (τ⇒! #'f))
               (define-values [r- t_r] (τ⇒app! f- (apply-current-subst t_f) #'e
                                               #:src this-syntax))]
         (attach-type r- t_r)])))

(define-syntax-parser def
  #:literals [:]
  [(_ id:id
      {~or {~once {~seq : {~type t:type}}}
           {~optional fixity:fixity-annotation}}
      ...
      e:expr)
   #:with id- (generate-temporary #'id)
   #:with id/prefix (generate-temporary #'id)
   #:with t-expr (preservable-property->expression (attribute t.τ))
   #`(begin-
       (define- id- (: e t))
       #,(indirect-infix-definition
          #'(define-syntax- id (make-typed-var-transformer #'id- t-expr))
          (attribute fixity.fixity)))]
  [(_ id:id
      {~optional fixity:fixity-annotation}
      e:expr)
   #:do [(define-values [e- t]
           (let-values ([(e- t) (τ⇒! #'e)])
             (values e- (apply-current-subst t))))]
   #:with id- (generate-temporary #'id)
   #:with id/prefix (generate-temporary #'id)
   #:with t-expr (preservable-property->expression (generalize t))
   #`(begin-
       (define- id- #,e-)
       #,(indirect-infix-definition
          #'(define-syntax- id
              (make-typed-var-transformer #'id- t-expr))
          (attribute fixity.fixity)))])

(define-syntax-parser let1
  #:literals [:]
  [(_ [id:id {~optional {~seq colon:: {~type t-ann:type}}} val:expr] body:expr)
   #:do [(define-values [val- t_val] (τ⇔! #'val (attribute t-ann.τ)))
         (match-define-values [(list id-) body- t_body]
           (τ⇔/λ! #'body (get-expected this-syntax) (list (cons #'id t_val))))]
   (~> (quasitemplate/loc this-syntax
         (let-values- ([(#,id-) #,val-]
                       {?? [() (begin- (λ- () t-ann.expansion) (values-))]})
           #,body-))
       (attach-type t_body)
       (syntax-property 'disappeared-use (and~> (attribute colon) syntax-local-introduce)))])

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

(define-syntax-parser letrec
  #:literals [:]
  [(_ ([id:id {~optional {~seq colon:: {~type t-ann:type}}} val:expr] ...+) body:expr)
   ; First, infer or check the type of each binding. Use τ⇐!\λ to check the type if a type annotation
   ; is provided. Otherwise, use τ⇒!/λ to infer it, and synthesize a fresh type variable for id’s
   ; type during inference. If a type is successfully inferred, unify it with the fresh type variable
   ; afterwards.
   #:do [; First, start by grouping bindings into two sets: those with explicit type annotations, and
         ; those without. For those without explicit type annotations, synthesize a fresh type
         ; variable to serve as their types.
         (define-values [ids+ts+vals/ann ids+ts+vals/unann]
           (let-values
               ([(ids+ts+vals/ann ids+ts+vals/unann)
                 (for/fold ([ids+ts+vals/ann '()]
                            [ids+ts+vals/unann '()])
                           ([id (in-list (attribute id))]
                            [t-ann (in-list (attribute t-ann.τ))]
                            [val (in-list (attribute val))])
                   (if t-ann
                       (values (cons (list id t-ann val) ids+ts+vals/ann) ids+ts+vals/unann)
                       (let* ([t_val-id (generate-temporary)]
                              [t_val (τ:var^ t_val-id)])
                         (values ids+ts+vals/ann (cons (list id t_val val) ids+ts+vals/unann)))))])
             (values (reverse ids+ts+vals/ann) (reverse ids+ts+vals/unann))))

         ; Next, establish a dictionary mapping all bindings to their types. This will be used as a
         ; binding context when typechecking.
         (define ids+ts (map #{cons (first %) (second %)} (append ids+ts+vals/ann ids+ts+vals/unann)))
         ; We also need to produce a mapping of expressions to their annotations, plus the body. This
         ; will be handed off to the expander to be typechecked.
         (define es+ts
           (snoc (map #{cons (third %) (second %)} (append ids+ts+vals/ann ids+ts+vals/unann))
                 (cons #'body (get-expected this-syntax))))

         ; With the setup out of the way, we can now call τs⇔/λ! to perform the actual typechecking.
         (match-define-values [ids- (list vals- ... body-) (list _ ... t_body)]
           (τs⇔/λ! es+ts ids+ts))]

   ; Finally, expand to the runtime value.
   #:with [id- ...] ids-
   #:with [val- ...] vals-
   (~> (quasitemplate/loc this-syntax
         (letrec-values ([(id-) val-] ...
                         {?? [() (begin- (λ- () t-ann.expansion) (values-))]} ...)
           #,body-))
       (attach-type t_body)
       (syntax-property 'disappeared-use
                        (map syntax-local-introduce (filter values (attribute colon)))))])

(define-syntax-parser :infer/print-type
  [(_ e)
   (~> (τ⇒! #'e)
       (λ () _)
       (call-with-values _ list)
       second
       apply-current-subst
       τ->string
       displayln)
   #'(void)])
