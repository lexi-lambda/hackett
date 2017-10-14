#lang curly-fn racket/base

; This module contains the core implementation of the Hackett typechecker, as well as the core type
; representations. The Hackett typechecker operates using a mutable typechecker context implemented
; as a Racket parameter, which contains information about solutions for existing solver variables.
;
; The core typechecker implements typing subsumption rules and the constraint solver for resolving
; typeclass instances. Other functionality is deferred to the implementation site of Hackett forms.
; The functions that perform the actual process of type inference (via recursive expansion) are
; defined in hackett/private/base, and they provide the primary interface to the various typechecker
; functions in this module.

(require (for-template racket/base)
         (for-syntax racket/base
                     syntax/parse
                     syntax/transformer)
         data/gvector
         racket/contract
         racket/format
         racket/function
         racket/list
         racket/match
         racket/syntax
         racket/stxparam-exptime
         syntax/id-table
         syntax/parse
         threading

         hackett/private/util/list
         hackett/private/util/stx)

(provide (contract-out [struct τ:var ([x identifier?])]
                       [struct τ:var^ ([x^ identifier?])]
                       [struct τ:skolem ([x^ identifier?])]
                       [struct τ:con ([name identifier?] [constructors (or/c (listof syntax?) #f)])]
                       [struct τ:app ([a τ?] [b τ?])]
                       [struct τ:∀ ([x identifier?] [t τ?])]
                       [struct τ:qual ([constr constr?] [t τ?])]
                       [struct ctx:var ([x identifier?])]
                       [struct ctx:skolem ([x^ identifier?])]
                       [struct ctx:solution ([x^ identifier?] [t τ?])]
                       [struct class:info ([vars (listof identifier?)]
                                           [method-table immutable-free-id-table?]
                                           [superclasses (listof constr?)])]
                       [struct class:instance ([class class:info?]
                                               [vars (listof identifier?)]
                                               [subgoals (listof constr?)]
                                               [ts (listof (and/c τ? τ-mono?))]
                                               [dict-expr syntax?])])
         τ? τ=? constr? τ-mono? τ-vars^ τ->string τ-wf! current-τ-wf! τ:app* τ:-> τ:->? τ:->*
         generalize inst insts τ<:/full! τ<:/elaborate! τ<:! τ-inst-l! τ-inst-r!
         ctx-elem? ctx? ctx-elem=? ctx-member? ctx-remove
         ctx-find-solution current-ctx-solution apply-subst apply-current-subst
         current-type-context modify-type-context
         register-global-class-instance! lookup-instance!
         type type-transforming? parse-type τ-stx-token local-expand-type
         make-type-variable-transformer attach-type attach-expected get-type get-expected
         make-typed-var-transformer

         (for-template local-class-instances))

;; ---------------------------------------------------------------------------------------------------
;; type representation

; Bound type variables. In the type (forall [a] a), a is a τ:var until the forall is instantiated.
; These usually do not appear in typechecking (since they will be instantiated to τ:var^, τ:skolem, or
; a concrete type).
(struct τ:var (x) #:prefab)

; Solver variables, which represent some yet-unknown type. The typechecker will *solve* these
; variables as necessary as part of *unification*.
(struct τ:var^ (x^) #:prefab)

; Skolem, aka “rigid”, type variables, which represent a *specific* unknown type. While solver
; variables unify with *anything*, skolem type variables unify with *nothing* (except themselves).
; These are introduced by user-provided type annotations — for example, an identity function annotated
; with (forall [a] {a -> a}) will check the implementation against a fresh skolem variable for a.
;
; Since skolems are completely unique, this process ensures an implementation is suitably polymorphic.
; If a function typechecks with a skolem, it must work for *all* types, since the function cannot know
; anything about the skolem. This is in contrast to an ordinary solver variable: if we used a solver
; variable to check the identity function instead of a skolem, then the user could write code that
; would get the solver variable to unify with a single, concrete type (such as (λ [x] {x + 1})), which
; would defeat the whole point of the quantified type annotation.
(struct τ:skolem (x^) #:prefab)

; Type constructors, the primary building block that all concrete types are built out of. Type
; constructors may actually be types themselves (such as Unit, Integer, or String), or they may be
; “type functions” that accept other types to produce a concrete type (such as Tuple, Maybe, or List).
;
; Type constructors also store the names of their associated constructors, if they are ADTs. If not,
; the constructors field is #f.
(struct τ:con (name constructors) #:prefab)

; Type application, which represents the application of some type constructor to type arguments. For
; example, (Maybe Integer) is the application of the Maybe constructor to the Integer constructor.
; Type constructors are curried in the same way that value-level functions are, so type applications
; can be nested in a left-associative manner to represent applying a type to multiple arguments.
(struct τ:app (a b) #:prefab)

; Universal quantification over types. The primitive quantifier abstracts a single type variable
; within its type. Within t, (τ:var x) may appear.
(struct τ:∀ (x t) #:prefab)

; Qualified types, aka types with constraints. Currently, the only sort of constraint Hackett supports
; is typeclass constraints. Constraints themselves are represented as types, though they do not
; (directly) describe any terms. Typeclass names may serve as type constructors that can be applied
; to other types just like any others.
(struct τ:qual (constr t) #:prefab)

;; ---------------------------------------------------------------------------------------------------
;; type operations

(define (τ? x) ((disjoin τ:var? τ:var^? τ:skolem? τ:con? τ:app? τ:∀? τ:qual?) x))

; Compares two types for literal equality. This is a much more primitive notion than type
; “equivalence”, since it does not check alpha-equivalence. This means that (forall [a] a) and
; (forall [b] b) will be considered different types.
(define/contract τ=?
  (-> τ? τ? boolean?)
  (match-lambda**
   [[(τ:var x) (τ:var y)] (free-identifier=? x y)]
   [[(τ:var^ x^) (τ:var^ y^)] (free-identifier=? x^ y^)]
   [[(τ:skolem x^) (τ:skolem y^)] (free-identifier=? x^ y^)]
   [[(τ:con a _) (τ:con b _)] (free-identifier=? a b)]
   [[(τ:app a b) (τ:app c d)] (and (τ=? a c) (τ=? b d))]
   [[(τ:∀ x a) (τ:∀ y b)] (and (free-identifier=? x y) (τ=? a b))]
   [[_ _] #f]))

(define (constr? x) (τ? x)) ; TODO: change this when we add kinds to check that x has kind Constraint

; Determines if a type is monomorphic, which simply checks if the type contains any quantifiers.
(define/contract τ-mono?
  (-> τ? boolean?)
  (match-lambda
    [(τ:var _) #t]
    [(τ:var^ _) #t]
    [(τ:skolem _) #t]
    [(τ:con _ _) #t]
    [(τ:app a b) (and (τ-mono? a) (τ-mono? b))]
    [(τ:∀ _ _) #f]
    [(τ:qual a b) (and (τ-mono? a) (τ-mono? b))]))

; Returns all solver variables present in a type.
(define/contract τ-vars^
  (-> τ? (listof identifier?))
  (match-lambda
    [(τ:var _) '()]
    [(τ:var^ x^) (list x^)]
    [(τ:skolem _) '()]
    [(τ:con _ _) '()]
    [(τ:app a b) (remove-duplicates (append (τ-vars^ a) (τ-vars^ b)) free-identifier=?)]
    [(τ:∀ _ t) (τ-vars^ t)]
    [(τ:qual a b)
     (remove-duplicates (append (τ-vars^ a) (τ-vars^ b)) free-identifier=?)]))

(define/contract (τ->string t)
  (-> τ? string?)
  (format "~a" (τ->datum t)))

(define/contract (τ->datum t)
  (-> τ? any/c)
  (match t
    [(τ:var x) (syntax-e x)]
    [(τ:var^ x^) (string->symbol (format "~a^" (syntax-e x^)))]
    [(τ:skolem x^) (syntax-e x^)]
    [(τ:con name _) (syntax-e name)]
    [(? τ:app?)
     (let flatten-app ([t t])
       (match t
         [(τ:app a b) (append (flatten-app a) (list (τ->datum b)))]
         [other (list (τ->datum other))]))]
    [(τ:∀ x t)
     (let flatten-forall ([xs (list x)]
                          [t t])
       (match t
         [(τ:∀ x t) (flatten-forall (cons x xs) t)]
         [other `(∀ ,(map syntax-e (reverse xs)) ,(τ->datum t))]))]
    [(τ:qual constr t)
     (let flatten-qual ([constrs (list constr)]
                        [t t])
       (match t
         [(τ:qual constr t) (flatten-qual (cons constr constrs) t)]
         [other `(=> ,(map τ->datum (reverse constrs)) ,(τ->datum t))]))]))

(define/contract (apply-τ t ts)
  (-> τ? (listof τ?) τ?)
  (foldl t #{τ:app %2 %1} ts))
(define (unapply-τ t)
  (-> τ? (non-empty-listof τ?))
  (match t
    [(τ:app a b) (snoc (unapply-τ a) b)]
    [_ (list t)]))
(define-match-expander τ:app*
  (syntax-parser [(_ list-pats ...+) #'(app unapply-τ (list list-pats ...))])
  (make-variable-like-transformer #'apply-τ))

;; ---------------------------------------------------------------------------------------------------
;; type contexts

(struct ctx:var (x) #:prefab)
(struct ctx:skolem (x^) #:prefab)
(struct ctx:solution (x^ t) #:prefab)

(define (ctx-elem? x) ((disjoin ctx:var? ctx:skolem? ctx:solution?) x))
(define (ctx? x) ((listof ctx-elem?) x))
(define/contract ctx-elem=?
  (-> ctx-elem? ctx-elem? boolean?)
  (match-lambda**
   [[(ctx:var x) (ctx:var y)] (free-identifier=? x y)]
   [[(ctx:skolem x^) (ctx:skolem y^)] (free-identifier=? x^ y^)]
   [[(ctx:solution x^ a) (ctx:solution y^ b)] (and (free-identifier=? x^ y^) (τ=? a b))]
   [[_ _] #f]))
(define/contract (ctx-member? ctx elem)
  (-> ctx? ctx-elem? boolean?)
  (and (member elem ctx ctx-elem=?) #t))
(define/contract (ctx-remove ctx elem)
  (-> ctx? ctx-elem? ctx?)
  (remove elem ctx ctx-elem=?))

(define/contract (ctx-find-solution ctx x^)
  (-> ctx? identifier? (or/c τ? #f))
  (and~> (findf #{and (ctx:solution? %) (free-identifier=? x^ (ctx:solution-x^ %))} ctx)
         ctx:solution-t))
(define/contract (current-ctx-solution x^)
  (-> identifier? (or/c τ? #f))
  (ctx-find-solution (current-type-context) x^))

(define/contract (τ-wf! ctx t)
  (-> ctx? τ? void?)
  (match t
    [(τ:var x) (unless (ctx-member? ctx (ctx:var x))
                 (raise-syntax-error #f "unbound type variable" x))]
    [(τ:var^ _) (void)]
    [(τ:skolem x^) (unless (ctx-member? ctx (ctx:skolem x^))
                    (raise-syntax-error #f "skolem escaped its scope" x^))]
    [(τ:con _ _) (void)]
    [(τ:app a b) (τ-wf! ctx a) (τ-wf! ctx b)]
    [(τ:∀ x t) (τ-wf! (snoc ctx (ctx:var x)) t)]
    [(τ:qual a b) (τ-wf! ctx a) (τ-wf! ctx b)]))
(define/contract (current-τ-wf! t)
  (-> τ? void?)
  (τ-wf! (current-type-context) t))

(define/contract (apply-subst ctx t)
  (-> ctx? τ? τ?)
  (match t
    [(τ:var _) t]
    [(τ:var^ x^) (let ([s (ctx-find-solution ctx x^)])
                   (if s (apply-subst ctx s) t))]
    [(τ:skolem _) t]
    [(τ:con _ _) t]
    [(τ:app a b) (τ:app (apply-subst ctx a) (apply-subst ctx b))]
    [(τ:∀ x t) (τ:∀ x (apply-subst ctx t))]
    [(τ:qual a b) (τ:qual (apply-subst ctx a) (apply-subst ctx b))]))
(define (apply-current-subst t)
  (apply-subst (current-type-context) t))

(define/contract (generalize t)
  (-> τ? τ?)
  (let* ([xs^ (τ-vars^ t)]
         [xs (generate-temporaries xs^)]
         [subst (map #{ctx:solution %1 (τ:var %2)} xs^ xs)])
    (foldr τ:∀ (apply-subst subst t) xs)))

(define/contract (inst t x s)
  (-> τ? identifier? τ? τ?)
  (match t
    [(τ:var y) (if (free-identifier=? x y) s t)]
    [(τ:var^ _) t]
    [(τ:skolem _) t]
    [(τ:con _ _) t]
    [(τ:app a b) (τ:app (inst a x s) (inst b x s))]
    [(τ:∀ v t*) (τ:∀ v (inst t* x s))]
    [(τ:qual a b) (τ:qual (inst a x s) (inst b x s))]))

(define/contract (insts t x+ss)
  (-> τ? (listof (cons/c identifier? τ?)) τ?)
  (foldl #{inst %2 (car %1) (cdr %1)} t x+ss))

(define/contract current-type-context (parameter/c ctx?) (make-parameter '()))
(define/contract (modify-type-context f)
  (-> (-> ctx? ctx?) void?)
  (current-type-context (f (current-type-context))))

;; ---------------------------------------------------------------------------------------------------
;; instance contexts

(struct class:info (vars method-table superclasses) #:transparent
  #:property prop:procedure
  (λ (info stx)
    ((make-type-variable-transformer
      (τ:con (syntax-parse stx
               [id:id #'id]
               [(id:id . _) #'id])
             #f))
     stx)))
(struct class:instance (class vars subgoals ts dict-expr) #:transparent)

(define global-class-instances (make-gvector))
(define/contract (register-global-class-instance! instance)
  (-> class:instance? void?)
  (gvector-add! global-class-instances instance))

(module local-instances-stxparam racket/base
  (require (for-syntax racket/base) racket/stxparam)
  (provide local-class-instances)
  (define-syntax-parameter local-class-instances '()))
(require (for-template 'local-instances-stxparam))

(define/contract (current-class-instances)
  (-> (listof class:instance?))
  (append (gvector->list global-class-instances)
          (syntax-parameter-value #'local-class-instances)))

(define (current-instances-of-class class)
  (-> class:info? (listof class:instance?))
  (filter #{eq? class (class:instance-class %)} (current-class-instances)))

;; ---------------------------------------------------------------------------------------------------
;; function types

; Functions are the only truly “baked-in” types. They are handled specially by the typechecker in
; order to implement higher-rank polymorphism, so they are defined here.

(define τ:-> (τ:con #'-> #f))

(define (mk-τ:-> a b) (τ:app (τ:app τ:-> a) b))
(define-match-expander τ:->*
  (syntax-parser
    [(_ a b)
     #'(τ:app (τ:app (== τ:-> τ=?) a) b)])
  (make-variable-like-transformer #'mk-τ:->))

(define τ:->?
  (match-lambda
    [(τ:->* _ _) #t]
    [_ #f]))

;; ---------------------------------------------------------------------------------------------------
;; subsumption, instantiation, and elaboration

(define/contract (τ<:/full! a b #:src src #:elaborate? elaborate?)
  (->i ([a τ?]
        [b τ?]
        #:src [src syntax?]
        #:elaborate? [elaborate? boolean?])
       [result (elaborate?) (if elaborate? (listof constr?) void?)])
  (define no-op (if elaborate? '() (void)))
  (match* [(apply-current-subst a) (apply-current-subst b)]
    ; <:Con
    [[(? τ:con? a) (? τ:con? b)]
     #:when (τ=? a b)
     no-op]
    ; <:Var
    [[(τ:var x) (τ:var y)]
     #:when (free-identifier=? x y)
     no-op]
    ; <:Exvar
    [[(τ:var^ x^) (τ:var^ y^)]
     #:when (free-identifier=? x^ y^)
     no-op]
    [[(τ:skolem x^) (τ:skolem y^)]
     #:when (free-identifier=? x^ y^)
     no-op]
    ; <:→
    ; we need to handle → specially since it is allowed to be applied to polytypes
    [[(τ:->* a b) (τ:->* c d)]
     (τ<:! c a #:src src)
     (τ<:! b d #:src src)
     no-op]
    ; <:App
    [[(τ:app a b) (τ:app c d)]
     (for ([t (in-list (list a b c d))])
       (unless (τ-mono? t)
         (raise-syntax-error #f (~a "illegal polymorphic type " (τ->string t)
                                    ", impredicative polymorphism is not supported") src)))
     (τ<:! a c #:src src)
     (τ<:! b d #:src src)
     no-op]
    ; <:∀L
    [[(τ:∀ x a) b]
     (let* ([x^ (generate-temporary x)]
            [a* (inst a x (τ:var^ x^))])
       (τ<:/full! a* b #:src src #:elaborate? elaborate?))]
    ; <:∀R
    [[a (τ:∀ x b)]
     (let* ([x^ (generate-temporary x)]
            [b* (inst b x (τ:skolem x^))])
       (modify-type-context #{snoc % (ctx:skolem x^)})
       (begin0
         (τ<:/full! a b* #:src src #:elaborate? elaborate?)
         (modify-type-context #{ctx-remove % (ctx:skolem x^)})))]
    ; <:Qual
    [[(τ:qual constr a) b]
     #:when elaborate?
     (snoc (τ<:/elaborate! a b #:src src) constr)]
    ; <:InstantiateL
    [[(τ:var^ x^) a]
     #:when (not (member x^ (τ-vars^ a) free-identifier=?))
     (τ-inst-l! x^ a)
     no-op]
    ; <:InstantiateR
    [[a (τ:var^ x^)]
     #:when (not (member x^ (τ-vars^ a) free-identifier=?))
     (τ-inst-r! a x^)
     no-op]
    [[a b]
     (raise-syntax-error 'typechecker
                         (~a "type mismatch\n"
                             "  between: " (τ->string a) "\n"
                             "      and: " (τ->string b))
                         src)]))

(define/contract (τ<:/elaborate! a b #:src src)
  (-> τ? τ? #:src syntax? (listof constr?))
  (τ<:/full! a b #:src src #:elaborate? #t))

(define/contract (τ<:! a b #:src src)
  (-> τ? τ? #:src syntax? void?)
  (τ<:/full! a b #:src src #:elaborate? #f))

(define/contract (τ-inst-l! x^ t)
  (-> identifier? τ? void?)
  (match t
    ; InstLSolve
    [(? τ-mono?)
     (modify-type-context #{snoc % (ctx:solution x^ t)})]
    ; InstLArr
    [(τ:->* a b)
     (let ([x1^ (generate-temporary x^)]
           [x2^ (generate-temporary x^)])
       (modify-type-context #{snoc % (ctx:solution x^ (τ:->* (τ:var^ x1^) (τ:var^ x2^)))})
       (τ-inst-r! a x1^)
       (τ-inst-l! x2^ (apply-current-subst b)))]
    ; InstLAllR
    [(τ:∀ x t*)
     (modify-type-context #{snoc % (ctx:var x)})
     (τ-inst-l! x^ t*)
     (modify-type-context #{ctx-remove % (ctx:var x)})]
    [_ (error 'τ-inst-l! (format "internal error: failed to instantiate ~a to a subtype of ~a"
                                 (τ->string (τ:var^ x^)) (τ->string t)))]))

(define/contract (τ-inst-r! t x^)
  (-> τ? identifier? void?)
  (match t
    ; InstRSolve
    [(? τ-mono?)
     (modify-type-context #{snoc % (ctx:solution x^ t)})]
    ; InstRArr
    [(τ:->* a b)
     (let ([x1^ (generate-temporary x^)]
           [x2^ (generate-temporary x^)])
       (modify-type-context #{snoc % (ctx:solution x^ (τ:->* (τ:var^ x1^) (τ:var^ x2^)))})
       (τ-inst-l! x1^ a)
       (τ-inst-r! (apply-current-subst b) x2^))]
    ; InstRAllL
    [(τ:∀ x t*)
     (let ([y^ (generate-temporary x)])
       (τ-inst-r! (inst t* x (τ:var^ y^)) x^))]
    [_ (error 'τ-inst-r! (format "internal error: failed to instantiate ~a to a supertype of ~a"
                                 (τ->string (τ:var^ x^)) (τ->string t)))]))

;; ---------------------------------------------------------------------------------------------------

; Attempts to unify a type with an instance head with a type for the purposes of picking a typeclass.
; If the match succeeds, it returns a list of instantiated subgoals for the instance, otherwise it
; returns #f.
(define/contract (unify-instance-head ts vars subgoals head)
  (-> (listof τ?) (listof identifier?) (listof constr?) (listof (and/c τ? τ-mono?))
      (or/c (listof constr?) #f))
  (let* ([vars^ (generate-temporaries vars)]
         [var-subst (map #{cons %1 (τ:var^ %2)} vars vars^)]
         [head-inst (map #{insts % var-subst} head)]
         [subgoals-inst (map #{insts % var-subst} subgoals)])
    (and (for/and ([t (in-list ts)]
                   [head-t (in-list head-inst)])
           (let loop ([t t]
                      [head-t head-t])
             (match* [(apply-current-subst t) (apply-current-subst head-t)]
               [[(τ:skolem x^) (τ:skolem y^)]
                #:when (free-identifier=? x^ y^)
                #t]
               [[(? τ-mono? t) (τ:var^ x^)]
                (modify-type-context #{snoc % (ctx:solution x^ t)})
                #t]
               [[(? τ:con? a) (? τ:con? b)]
                #:when (τ=? a b)
                #t]
               [[(τ:app a b) (τ:app c d)]
                (and (loop a c) (loop b d))]
               [[_ _]
                #f])))
         subgoals-inst)))

(define/contract (lookup-instance! constr #:src src)
  (-> constr? #:src syntax? (values class:instance? (listof constr?)))
  (match-define (τ:app* (τ:con class-id _) (app apply-current-subst ts) ...) constr)
  (define class (syntax-local-value class-id)) ; FIXME: handle when this isn’t a class:info
  (apply values
         (or (for/or ([instance (in-list (current-instances-of-class class))])
               (let ([old-type-context (current-type-context)])
                 (let ([constrs (unify-instance-head ts
                                                     (class:instance-vars instance)
                                                     (class:instance-subgoals instance)
                                                     (class:instance-ts instance))])
                   (if constrs (list instance constrs)
                       (begin (current-type-context old-type-context) #f)))))
             (raise-syntax-error 'typechecker
                                 (~a "could not deduce " (τ->string (apply-current-subst constr)))
                                 src))))

;; ---------------------------------------------------------------------------------------------------
;; parsing types

; Types are represented using the data structures defined at the top of this module. However, users
; use a different source language for writing types that does not use the raw type data structures
; directly. This code handles “parsing” such type syntax, though types are not really parsed: they are
; *expanded*.
;
; Type syntax in Hackett actually uses arbitrary Racket expressions that are expanded as part of the
; typechecking process. They are expected to attach a syntax property to their expansion that
; represents the resulting type. When types are being expanded, (type-transforming?) will be #t, which
; Hackett uses to invoke a custom #%app that converts application expressions to uses of τ:app.

(define type-transforming?-param (make-parameter #f))
(define (type-transforming?) (type-transforming?-param))

(define-syntax-class (type [intdef-ctx #f])
  #:attributes [τ expansion]
  #:opaque
  [pattern t:expr
           #:with expansion (local-expand-type #'t intdef-ctx)
           #:attr τ (syntax-property (attribute expansion) 'τ)
           #:when (τ? (attribute τ))])

(define (parse-type stx)
  (syntax-parse stx
    #:context 'parse-type
    [t:type (attribute t.τ)]))

(define/contract (local-expand-type stx [intdef-ctx #f])
  (->* [syntax?] [(or/c internal-definition-context? #f)] syntax?)
  (parameterize ([type-transforming?-param #t])
    (local-expand stx 'expression '() intdef-ctx)))

(define/contract (make-type-variable-transformer t)
  (-> τ? any)
  (make-variable-like-transformer (τ-stx-token t)))

;; -------------------------------------------------------------------------------------------------

(define/contract (τ-stx-token t #:expansion [stx #'(void)])
  (->* [τ?] [#:expansion syntax?] syntax?)
  (syntax-property stx 'τ t))
(define/contract (attach-type stx t)
  (-> syntax? τ? syntax?)
  (syntax-property stx ': t))
(define/contract (attach-expected stx t)
  (-> syntax? τ? syntax?)
  (syntax-property stx ':⇐ t))

(define/contract (get-type stx)
  (-> syntax? (or/c τ? #f))
  (let loop ([val (syntax-property stx ':)])
    (if (pair? val) (loop (car val)) val)))
(define/contract (get-expected stx)
  (-> syntax? (or/c τ? #f))
  (let loop ([val (syntax-property stx ':⇐)])
    (if (pair? val) (loop (car val)) val)))

(define/contract (make-typed-var-transformer x t)
  (-> identifier? τ? any)
  (make-variable-like-transformer (attach-type x t)))
