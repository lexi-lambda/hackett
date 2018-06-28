#lang curly-fn racket/base

; This module defines data structures to represent classes and instances, global and local instance
; contexts, and functions for solving constraints by looking up instances. Additionally there are
; functions for reducing redundant instance contexts.

(require (for-template racket/base
                       syntax/id-table)

         data/gvector
         racket/contract
         racket/format
         racket/list
         racket/match
         racket/set
         racket/struct
         syntax/id-set
         syntax/id-table
         syntax/parse
         syntax/parse/class/local-value

         hackett/private/typecheck
         hackett/private/util/contract
         hackett/private/util/stx)

(provide (contract-out
          [struct functional-dependency ([determiners immutable-free-id-set?]
                                         [determined immutable-free-id-set?])]
          [struct class:info ([vars (listof identifier?)]
                              [method-table immutable-free-id-table?]
                              [default-methods immutable-free-id-table?]
                              [superclasses (listof constr?)]
                              [functional-dependencies (immutable-set/c functional-dependency?)]
                              [candidate-keys (immutable-set/c immutable-free-id-set?)]
                              [deriving-transformer (or/c (-> syntax? syntax?) #f)])]
          [struct class:instance ([class-id identifier?]
                                  [vars (listof identifier?)]
                                  [subgoals (listof constr?)]
                                  [ts (listof (and/c type? type-mono?))]
                                  [dict-expr syntax?])])
         make-class:info class:instance->string
         register-global-class-instance! current-local-class-instances
         constr->instances lookup-instance! lookup-overlapping-instances
         reduce-context type-reduce-context
         (for-template @%superclasses-key))

;; ---------------------------------------------------------------------------------------------------
;; classes

(struct functional-dependency (determiners determined) #:transparent
  #:property prop:custom-write
  (make-constructor-style-printer
   (λ (fundep) 'functional-dependency)
   (λ (fundep) (list (free-id-set->list (functional-dependency-determiners fundep))
                     (free-id-set->list (functional-dependency-determined fundep))))))

(struct class:info
  (vars                    ; class variable identifiers, in order; may appear free in method types
   method-table            ; identifier table that maps method names to method types
   default-methods         ; identifier table that maps method names to default implementations
   superclasses            ; list of superclass constraints instances must satisfy
   functional-dependencies ; set of dependencies between class parameters
   candidate-keys          ; set of minimal sets of parameters that determine all other parameters
   deriving-transformer)   ; syntax transformer used for deriving this class, or #f
  #:transparent
  #:property prop:procedure
  (λ (info stx)
    ((make-variable-like-transformer
      #`(#%type:con #,(syntax-parse stx
                        [id:id #'id]
                        [(id:id . _) #'id])))
     stx)))

(define/contract (make-class:info vars method-table default-methods superclasses
                                  functional-dependencies deriving-transformer)
  (-> (listof identifier?)
      immutable-free-id-table?
      immutable-free-id-table?
      (listof constr?)
      (immutable-set/c functional-dependency?)
      (or/c (-> syntax? syntax?) #f)
      class:info?)
  (class:info vars method-table default-methods superclasses functional-dependencies
              (compute-candidate-keys (immutable-free-id-set vars) functional-dependencies)
              deriving-transformer))

; Computes the closure of a set of attributes with respect to a set of functional dependencies. That
; it, given a set of functional dependencies, computes which parameters of a class can be determined
; from a set of known parameters.
;
; For example, given a class, C a b c, and a set of functional dependencies, a -> b, b -> c, then the
; closure of {a} is {a, b, c}, the closure of {b} is {b, c}, and the closure of {c} is {c}.
(define/contract (compute-functional-dependency-closure attrs fundeps)
  (-> immutable-free-id-set? (immutable-set/c functional-dependency?) immutable-free-id-set?)
  (let loop ([closure attrs])
    (define closure*
      (for/fold ([closure closure])
                ([fundep (in-set fundeps)])
        (if (for/and ([x (in-free-id-set (functional-dependency-determiners fundep))])
              (free-id-set-member? closure x))
            (for/fold ([closure closure])
                      ([x (in-free-id-set (functional-dependency-determined fundep))])
              (free-id-set-add closure x))
            closure)))
    (if (> (free-id-set-count closure*)
           (free-id-set-count closure))
        (loop closure*)
        closure*)))

; Computes the set of candidate keys for a set of attributes, given a set of functional dependencies.
; A candidate key is a minimal set of attributes from which all attributes can be derived. In the
; context of typeclasses, this corresponds to the sets of class parameters that can fully determine an
; instance.
(define/contract (compute-candidate-keys attrs fundeps)
  (-> immutable-free-id-set?
      (immutable-set/c functional-dependency?)
      (immutable-set/c immutable-free-id-set?))
  (define (minimize attrs)
    (let ([closure (compute-functional-dependency-closure (immutable-free-id-set attrs) fundeps)])
      (let loop ([attrs attrs]
                 [keep '()])
        (if (empty? attrs)
            (immutable-free-id-set keep)
            (let* ([attrs* (rest attrs)]
                   [closure* (compute-functional-dependency-closure
                              (immutable-free-id-set (append attrs* keep))
                              fundeps)])
              (if (free-id-set=? closure closure*)
                  (loop attrs* keep)
                  (loop attrs* (cons (first attrs) keep))))))))
  (for/set ([attrs (in-permutations (free-id-set->list attrs))])
    (minimize attrs)))

;; ---------------------------------------------------------------------------------------------------
;; instances

(struct class:instance (class-id vars subgoals ts dict-expr) #:transparent)

(define/contract (class:instance->string v)
  (-> class:instance? string?)
  (with-syntax ([class-id (class:instance-class-id v)]
                [[var ...] (class:instance-vars v)]
                [[t ...] (class:instance-ts v)])
    (type->string #'(?#%type:forall* [var ...] (?#%type:app* (#%type:con class-id) t ...)))))

(define-syntax-class (class-id #:require-deriving-transformer? [require-deriving-transformer? #f])
  #:description "class id"
  #:attributes [local-value]
  [pattern
   {~var || (local-value class:info? #:failure-message "identifier was not bound to a class")}
   #:fail-unless (or (not require-deriving-transformer?)
                     (class:info-deriving-transformer (attribute local-value)))
                 "class is not derivable"])

(define global-class-instances (make-gvector))
(define/contract (register-global-class-instance! instance)
  (-> class:instance? void?)
  (gvector-add! global-class-instances instance))

(define/contract current-local-class-instances
  (parameter/c (listof class:instance?))
  (make-parameter '()))

(define/contract (current-class-instances)
  (-> (listof class:instance?))
  (append (current-local-class-instances)
          (gvector->list global-class-instances)))

(define (current-instances-of-class class)
  (-> class:info? (listof class:instance?))
  (filter #{eq? class (syntax-local-value (class:instance-class-id %))} (current-class-instances)))

(module superclasses-key racket/base
  (require (for-syntax racket/base))
  (provide @%superclasses-key)
  (define-syntax (@%superclasses-key stx)
    (raise-syntax-error #f "cannot be used as an expression" stx)))
(require (for-template 'superclasses-key))

(define/contract constr->class-id+info+ts
  (-> constr? (values identifier? class:info? (listof type?)))
  (syntax-parser
    #:context 'constr->class:info
    #:literal-sets [type-literals]
    [(~#%type:app* (#%type:con class-id:class-id) ts ...)
     (values #'class-id (attribute class-id.local-value) (attribute ts))]))

; Given a constraint, calculate the instances it brings in scope, including instances that can be
; derived via superclasses. For example, the constraint (Monad m) brings in three instances, one for
; Monad and two for Functor and Applicative.
(define/contract (constr->instances constr dict-expr)
  (-> constr? syntax? (listof class:instance?))
  (let-values ([(class-id class-info ts) (constr->class-id+info+ts constr)])
    (let* ([ts* (map apply-current-subst ts)]
           [instance (class:instance class-id '() '() ts* dict-expr)]
           ; instantiate the superclass constraints, so for (Monad Unit), we get (Applicative Unit)
           ; instead of (Applicative m)
           [insts-dict (map cons (class:info-vars class-info) ts*)]
           [super-constrs (map #{insts % insts-dict} (class:info-superclasses class-info))]
           [superclass-dict-expr #`(free-id-table-ref #,dict-expr #'@%superclasses-key)]
           [super-instances (for/list ([(super-constr i) (in-indexed (in-list super-constrs))])
                              (constr->instances
                               super-constr
                               #`(vector-ref #,superclass-dict-expr '#,i)))])
      (cons instance (append* super-instances)))))

; Checks if any declared instances of the given class would overlap if a new instance were declared
; with the given instance head.
(define/contract (lookup-overlapping-instances class head)
  (-> class:info? (listof type?) (listof class:instance?))
  (for/fold ([result '()]
             #:result (reverse result))
            ([instance (in-list (current-instances-of-class class))])
    (if (instances-overlap? (class:info-vars class)
                            (class:info-candidate-keys class)
                            head
                            (class:instance-ts instance))
        (cons instance result)
        result)))

; Checks if two instance heads overlap, using the class’s candidate keys to determine which parts of
; the head may match. Quantified variables in the heads should not be instantiated; this function
; assumes any such variables will be free in the heads.
(define/contract (instances-overlap? class-vars candidate-keys head-a head-b)
  (-> (listof identifier?)
      (immutable-set/c immutable-free-id-set?)
      (listof type?)
      (listof type?)
      boolean?)
  (for/or ([candidate-key (in-set candidate-keys)])
    (for/and ([class-var (in-list class-vars)]
              [ta (in-list head-a)]
              [tb (in-list head-b)]
              #:when (free-id-set-member? candidate-key class-var))
      (let loop ([ta ta] [tb tb])
        (or (type=? ta tb)
            (syntax-parse (list ta tb)
              #:literal-sets [type-literals]
              [[_:id _] #t]
              [[_ _:id] #t]
              [[(#%type:app a b) (#%type:app c d)]
               (and (loop #'a #'c)
                    (loop #'b #'d))]
              [[_ _] #f]))))))

;; ---------------------------------------------------------------------------------------------------
;; instance lookup / constraint solving

; During elaboration, Hackett performs constraint solving, which involves selecting a typeclass
; instance that matches each constraint and inserting the relevant dictionary into the program in the
; appropriate place. An instance can be made available one of two ways:
;
;   1. Module-level instance declarations provide globally-applicable instances. These are what users
;      usually think about when they reason about typeclass instances, since they provide the actual
;      definitions of typeclass behavior, and they are always written explicitly by the user in the
;      source program.
;
;      Instance declarations may have subgoals, which require additional constraints to be solved.
;      For example, solving (Show (Maybe a)) requires solving (Show a). Importantly, however, the
;      solvability of subgoals never has any effect on which instance is selected! An instance is
;      chosen and committed to without considering subgoals; if a subgoal later fails to solve, the
;      constraint solver does NOT backtrack. This is important for both performance (needing to be
;      able to unwind the solver at any point in time would be expensive) and for keeping constraint
;      solving predictable (it makes it easier to detect and prevent overlapping instances).
;
;   2. Polymorphic values may provide local instances. These are values that include typeclass
;      constraints in their type signatures, such as (forall [f] (Applicative f) => (f Unit)). These
;      values are transformed into functions that accept a dictionary as an argument and use it to
;      perform dynamic dispatch, so that dictionary is available inside the implementation of the
;      value. Local instances never have subgoals.
;
; In both cases, constraint solving fundamentally reduces to a two-step process: looking up all
; instances in scope for a given class, then matching the constraint against each instance’s head to
; find which instances match. This matching process is delicate — we want to perform one-way matching,
; not unification, since we don’t want constraint solving to specialize user’s types.
;
; To give an example, imagine the user writes the expression (show mempty). Since mempty has type
; (forall [a] (Monoid a) => a), it will be instantiated with a fresh type variable, a1. This will lead
; to the constraints (Monoid a1), from the use of mempty, and (Show a1), from the use of show, and a1
; will never be further constrained.
;
; When we attempt to solve these constraints, we may examine instances such as (Monoid Unit) and
; (Monoid String), which both apply, so we should not select either instance. This goes beyond the
; problem of mere overlap, however, since even if one instance unambiguously applied, a user could
; always add a new instance declaration later. We don’t want new instance declarations to change the
; behavior of an existing program, so such an instance should be rejected out of hand.
;
; Functional dependencies add a small twist to the above rule, since fundeps may indeed introduce new
; unifications during the constraint solving process. When solving a constraint like
; (Monad-Reader t1 (-> String)), we can pick the (forall [r] (Monad-Reader r (-> r)) instance even
; though it requires solving t1 to String, since instance selection is weakened by the functional
; dependency between the second and first parameters of Monad-Reader. While this may seem inconsistent
; with the principle that we avoid unifying types that come from the constraint, it is actually
; perfectly fine: unification still only happens after we’ve already committed to an instance, so it
; does not affect instance selection.

(define/contract (lookup-instance!
                  constr
                  #:src src
                  #:failure-thunk [failure-thunk #f])
  (->* [constr? #:src syntax?]
       [#:failure-thunk (or/c (-> any) #f)]
       any) ; (values class:instance? (listof constr?))
  (match-define-values [_ class ts] (constr->class-id+info+ts constr))
  (define instance+subgoals
    (for/or ([instance (in-list (current-instances-of-class class))])
      (let ([constrs (unify-instance-head! (class:info-vars class)
                                           (class:info-candidate-keys class)
                                           ts
                                           (class:instance-vars instance)
                                           (class:instance-subgoals instance)
                                           (class:instance-ts instance)
                                           #:src src)])
        (and constrs (list instance constrs)))))
  (if instance+subgoals
      (apply values instance+subgoals)
      (if failure-thunk
          (failure-thunk)
          (raise-syntax-error 'typechecker
                              (~a "could not deduce " (type->string (apply-current-subst constr)))
                              src))))

; Attempts to unify a type with an instance head with a type for the purposes of picking a typeclass.
; If the match succeeds, it returns a list of instantiated subgoals for the instance, otherwise it
; returns #f.
(define/contract (unify-instance-head! class-vars class-candidate-keys constr-ts
                                       instance-vars instance-subgoals instance-head
                                       #:src src)
  (-> (listof identifier?)
      (immutable-set/c immutable-free-id-set?)
      (listof type?)
      (listof identifier?)
      (listof constr?)
      (listof (and/c type? type-mono?))
      #:src syntax?
      (or/c (listof constr?) #f))
  (let* (; Start by instantiating any variables that appear in the instance and its subgoals.
         [vars^ (generate-temporaries instance-vars)]
         [var-subst (map #{cons %1 #`(#%type:wobbly-var #,%2)} instance-vars vars^)]
         [head-inst (map #{insts % var-subst} instance-head)]
         [subgoals-inst (map #{insts % var-subst} instance-subgoals)]
         ; Next, see if the instance actually matches the types in the constraint. In the presence of
         ; functional dependencies, not all types in the head necessarily have to match, so try the
         ; candidate keys, instead.
         [old-type-context (current-type-context)]
         [matching-types (for/or ([candidate-key (in-set class-candidate-keys)])
                           (if (for/and ([class-var (in-list class-vars)]
                                         [t_head (in-list head-inst)]
                                         [t_constr (in-list constr-ts)]
                                         #:when (free-id-set-member? candidate-key class-var))
                                 (types-match?! t_head t_constr))
                               candidate-key
                               (begin
                                 (current-type-context old-type-context)
                                 #f)))])
    ; If the instance matched, unify the types in the head with the types in the constraint that
    ; weren’t part of the candidate key.
    (and matching-types
         (begin
           (for ([class-var (in-list class-vars)]
                 [t_head (in-list head-inst)]
                 [t_constr (in-list constr-ts)]
                 #:when (not (free-id-set-member? matching-types class-var)))
             (type<:! t_constr t_head #:src src))
           subgoals-inst))))

;; ---------------------------------------------------------------------------------------------------

; Performs one-way matching to see if a type matches another one. Unlike unification, one-way matching
; is asymmetric: it only solves wobbly variables in the first type argument, never in the second. If
; unifying the two types would require unification in the second type, matching fails. Also, matching
; is more restricted than unification: it never instantiates quantifiers in other type, nor does it
; permit qualified types. If a quantifier or qualified type is encountered, matching fails.
(define/contract (types-match?! a b)
  (-> type? type? boolean?)
  (syntax-parse (list (apply-current-subst a) (apply-current-subst b))
    #:context 'types-match?!
    #:literal-sets [type-literals]
    [[(#%type:rigid-var x^) (#%type:rigid-var y^)]
     #:when (free-identifier=? #'x^ #'y^)
     #t]
    [[(#%type:wobbly-var x^) t]
     #:when (type-mono? #'t)
     (type-inst-l! #'x^ #'t)
     #t]
    [[(#%type:con a) (#%type:con b)]
     #:when (free-identifier=? #'a #'b)
     #t]
    [[(#%type:app a b) (#%type:app c d)]
     (and (types-match?! #'a #'c) (types-match?! #'b #'d))]
    [[_ _]
     #f]))

;; ---------------------------------------------------------------------------------------------------
;; context reduction

; Context reduction is the process of simplifying contexts by pruning unnecessary constraints.
; Removing these constraints reduces the number of dictionaries that need to be passed, which is
; especially important in macro-enabled Hackett, since users might write macros that expand to
; constraints with redundant or otherwise unnecessary information. To avoid placing an unreasonable
; burden on macro authors to intelligently prune these contexts themselves, Hackett guarantees it will
; perform a certain amount of context reduction automatically.
;
; Implementing context reduction is a problem with a large design space, but fortunately, the various
; choices and their tradeoffs have been covered extensively in the paper “Type classes: an exploration
; of the design space”, available here:
;
;   https://www.microsoft.com/en-us/research/wp-content/uploads/1997/01/multi.pdf
;
; Hackett implements context reduction based on the following rules:
;
;   1. Duplication constraint elimination. For example, the type:
;
;        (forall [a] (Eq a) (Eq a) => ....)
;
;      ...can be simplified to this type:
;
;        (forall [a] (Eq a) => ....)
;
;   2. Superclass subsumption. Since subclass dictionaries include dictionaries for their
;      superclasses, superclass constraints can be eliminated in favor of equivalent subclass ones.
;      For example, the type:
;
;        (forall [f] (Functor f) (Applicative f) => ....)
;
;      ...can be simplified to this type:
;
;        (forall [f] (Applicative f) => ....)
;
;   3. Discharging tautological constraints. A tautological constraint is a constraint that can be
;      immediately resolved via an in-scope instance declaration. For example, the constraint
;      (Eq Integer) always holds, so there is never any reason to include it in a context.
;
;      This is complicated slightly by the fact that instances can also have contexts, so for a
;      constraint to be tautological, all constraints in the chosen instance context must also be
;      tautological. For example, given an instance:
;
;        (instance (forall [a] (Eq a) => (Foo (Tuple a b))) ....)
;
;      ...the constraint (Foo (Tuple Integer t)) is tautological regardless of t, since (Eq Integer)
;      is tautological.

(define/contract (constr-tautological? constr #:extra-constrs [extra-constrs '()])
  (->* [constr?] [#:extra-constrs (listof constr?)] boolean?)
  (or (ormap #{type=? constr %} extra-constrs)
      (match/values (lookup-instance! constr #:src #'here #:failure-thunk (λ () (values #f #f)))
        [[#f _] #f]
        [[_ subgoals] (andmap constr-tautological? subgoals)])))

(define/contract (superclasses-entail? constr-a constr-b)
  (-> constr? constr? boolean?)
  (match-let-values ([(_ class ts) (constr->class-id+info+ts constr-a)])
    (let* ([inst-dict (map cons (class:info-vars class) ts)]
           [supers (map #{insts % inst-dict} (class:info-superclasses class))])
      (or (ormap #{types-match?! % constr-b} supers)
          (ormap #{superclasses-entail? % constr-b} supers)))))

(define/contract (constrs-entail? constrs constr)
  (-> (listof constr?) constr? boolean?)
  (and (or (member constr constrs type=?)
           (ormap #{superclasses-entail? % constr} constrs))
       #t))

(define/contract (reduce-context constrs
                                 #:extra-tautological-constrs [extra-tautological-constrs '()])
  (->* [(listof constr?)] [#:extra-tautological-constrs (listof constr?)] (listof constr?))
  (let loop ([constrs constrs]
             [constrs* '()])
    (match constrs
      [(cons constr remaining-constrs)
       (loop remaining-constrs
             (let ([reduced-context (append remaining-constrs constrs*)])
               (if (or (constr-tautological?
                        constr
                        #:extra-constrs (append reduced-context extra-tautological-constrs))
                       (constrs-entail? reduced-context constr))
                   constrs*
                   (cons constr constrs*))))]
      [_
       (reverse constrs*)])))

(define/contract type-reduce-context
  (-> type? type?)
  (syntax-parser
    #:context 'type-reduce-context
    [(~#%type:forall* [x ...] {~and t_qual (~#%type:qual* [constr ...] t)})
     #:with [constr* ...] (reduce-context (attribute constr))
     (quasisyntax/loc/props this-syntax
       (?#%type:forall* [x ...] #,(syntax/loc/props #'t_qual
                                    (?#%type:qual* [constr* ...] t))))]))
