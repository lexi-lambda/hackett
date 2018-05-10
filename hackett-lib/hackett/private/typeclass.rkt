#lang curly-fn racket/base

; This module defines data structures to represent classes and instances, global and local instance
; contexts, and functions for solving constraints by looking up instances. Additionally there are
; functions for reducing redundant instance contexts.

(require (for-template racket/base
                       syntax/id-table
                       hackett/private/type-language)

         data/gvector
         racket/contract
         racket/list
         racket/match
         racket/format
         racket/stxparam-exptime
         syntax/parse
         syntax/parse/class/local-value
         syntax/id-table

         hackett/private/typecheck
         hackett/private/util/list
         hackett/private/util/stx)

(provide (contract-out [struct class:info ([vars (listof identifier?)]
                                           [method-table immutable-free-id-table?]
                                           [default-methods immutable-free-id-table?]
                                           [superclasses (listof constr?)]
                                           [deriving-transformer (or/c (-> syntax? syntax?) #f)])]
                       [struct class:instance ([class class:info?]
                                               [vars (listof identifier?)]
                                               [subgoals (listof constr?)]
                                               [ts (listof (and/c type? type-mono?))]
                                               [dict-expr syntax?])])
         register-global-class-instance! constr->instances lookup-instance!
         reduce-context type-reduce-context
         (for-template local-class-instances @%superclasses-key))

;; ---------------------------------------------------------------------------------------------------
;; instance contexts

(struct class:info (vars method-table default-methods superclasses deriving-transformer) #:transparent
  #:property prop:procedure
  (λ (info stx)
    ((make-variable-like-transformer
      #`(#%type:con #,(syntax-parse stx
                        [id:id #'id]
                        [(id:id . _) #'id])))
     stx)))
(struct class:instance (class vars subgoals ts dict-expr) #:transparent)

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

(module local-instances-stxparam racket/base
  (require (for-syntax racket/base) racket/stxparam)
  (provide local-class-instances)
  (define-syntax-parameter local-class-instances '()))
(require (for-template 'local-instances-stxparam))

(define/contract (current-class-instances)
  (-> (listof class:instance?))
  (append (syntax-parameter-value #'local-class-instances)
          (gvector->list global-class-instances)))

(define (current-instances-of-class class)
  (-> class:info? (listof class:instance?))
  (filter #{eq? class (class:instance-class %)} (current-class-instances)))


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
  (match-let-values ([(class ts) (constr->class:info+ts constr-a)])
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

;; ---------------------------------------------------------------------------------------------------
;; instances

(module superclasses-key racket/base
  (require (for-syntax racket/base))
  (provide @%superclasses-key)
  (define-syntax (@%superclasses-key stx)
    (raise-syntax-error #f "cannot be used as an expression" stx)))
(require (for-template 'superclasses-key))

(define/contract constr->class:info+ts
  (-> constr? (values class:info? (listof type?)))
  (syntax-parser
    #:context 'constr->class:info
    #:literal-sets [type-literals]
    [(~#%type:app* (#%type:con class-id:class-id) ts ...)
     (values (attribute class-id.local-value) (attribute ts))]))

; Given a constraint, calculate the instances it brings in scope, including instances that can be
; derived via superclasses. For example, the constraint (Monad m) brings in three instances, one for
; Monad and two for Functor and Applicative.
(define/contract (constr->instances constr dict-expr)
  (-> constr? syntax? (listof class:instance?))
  (let-values ([(class-info ts) (constr->class:info+ts constr)])
    (let* ([ts* (map apply-current-subst ts)]
           [instance (class:instance class-info '() '() ts* dict-expr)]
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

; Attempts to unify a type with an instance head with a type for the purposes of picking a typeclass.
; If the match succeeds, it returns a list of instantiated subgoals for the instance, otherwise it
; returns #f.
(define/contract (unify-instance-head ts vars subgoals head)
  (-> (listof type?) (listof identifier?) (listof constr?) (listof (and/c type? type-mono?))
      (or/c (listof constr?) #f))
  (let* ([vars^ (generate-temporaries vars)]
         [var-subst (map #{cons %1 #`(#%type:wobbly-var #,%2)} vars vars^)]
         [head-inst (map #{insts % var-subst} head)]
         [subgoals-inst (map #{insts % var-subst} subgoals)])
    (and (andmap types-match?! head-inst ts)
         subgoals-inst)))

(define/contract (lookup-instance!
                  constr
                  #:src src
                  #:failure-thunk [failure-thunk
                                   (λ ()
                                     (raise-syntax-error
                                      'typechecker
                                      (~a "could not deduce "
                                          (type->string (apply-current-subst constr)))
                                      src))])
  (->* [constr? #:src syntax?]
       [#:failure-thunk (-> any)]
       any) ; (values class:instance? (listof constr?))
  (define-values [class ts] (constr->class:info+ts constr))
  (define ts* (map apply-current-subst ts))
  (define instance+subgoals
    (for/or ([instance (in-list (current-instances-of-class class))])
      (let ([old-type-context (current-type-context)])
        (let ([constrs (unify-instance-head ts*
                                            (class:instance-vars instance)
                                            (class:instance-subgoals instance)
                                            (class:instance-ts instance))])
          (if constrs (list instance constrs)
              (begin (current-type-context old-type-context) #f))))))
  (if instance+subgoals
      (apply values instance+subgoals)
      (failure-thunk)))

;; ---------------------------------------------------------------------------------------------------

; Performs one-way unification to see if a type matches another one. Unlike general unification,
; one-way matching is asymmetric: it only solves wobbly variables in the first type argument, never in
; the second. If unifying the two types would require unification in the second type, matching fails.
; Also, matching is more restricted than unification: it never instantiates quantifiers in other type,
; nor does it permit qualified types. If a quantifier or qualified type is encountered, matching
; fails.
(define/contract (types-match?! a b)
  (-> type? type? boolean?)
  (syntax-parse (list (apply-current-subst a) (apply-current-subst b))
    #:context 'match-types!
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
