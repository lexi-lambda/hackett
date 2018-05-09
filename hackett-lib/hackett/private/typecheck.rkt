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

(require (for-template racket/base
                       syntax/id-table
                       hackett/private/type-language)
         (for-syntax racket/base
                     syntax/transformer)
         data/gvector
         racket/contract
         racket/format
         racket/function
         racket/list
         racket/match
         racket/string
         racket/syntax
         racket/stxparam-exptime
         syntax/id-table
         syntax/parse
         syntax/parse/class/local-value
         syntax/parse/define
         syntax/parse/experimental/template
         threading

         hackett/private/infix
         hackett/private/util/list
         hackett/private/util/stx)

(provide (contract-out [struct ctx:solution ([x^ identifier?] [t type?])]
                       [struct class:info ([vars (listof identifier?)]
                                           [method-table immutable-free-id-table?]
                                           [default-methods immutable-free-id-table?]
                                           [superclasses (listof constr?)]
                                           [deriving-transformer (or/c (-> syntax? syntax?) #f)])]
                       [struct class:instance ([class class:info?]
                                               [vars (listof identifier?)]
                                               [subgoals (listof constr?)]
                                               [ts (listof (and/c type? type-mono?))]
                                               [dict-expr syntax?])])
         type? type=? constr? type-mono? type-vars^ type->string
         generalize inst insts type<:/full! type<:/elaborate! type<:! type-inst-l! type-inst-r!
         ctx-elem? ctx? ctx-elem=? ctx-member? ctx-remove
         ctx-find-solution current-ctx-solution apply-subst apply-current-subst
         current-type-context modify-type-context
         register-global-class-instance! constr->instances lookup-instance!
         reduce-context type-reduce-context
         attach-type attach-expected get-type get-expected apply-current-subst-in-tooltips
         make-typed-var-transformer

         (for-template (all-from-out hackett/private/type-language)
                       local-class-instances @%superclasses-key))

;; ---------------------------------------------------------------------------------------------------
;; type operations

(define (type? x) (syntax? x))
(define (constr? x) (type? x))

; Compares two types for literal equality. This is a much more primitive notion than type
; “equivalence”, since it does not check alpha-equivalence. This means that (forall [a] a) and
; (forall [b] b) will be considered different types.
(define/contract (type=? a b)
  (-> type? type? boolean?)
  (syntax-parse (list a b)
    #:context 'type=?
    #:literal-sets [type-literals]
    [[x:id y:id] (free-identifier=? #'x #'y)]
    [[(#%type:wobbly-var x) (#%type:wobbly-var y)] (free-identifier=? #'x #'y)]
    [[(#%type:rigid-var x) (#%type:rigid-var y)] (free-identifier=? #'x #'y)]
    [[(#%type:con a) (#%type:con b)] (free-identifier=? #'a #'b)]
    [[(#%type:app a b) (#%type:app c d)] (and (type=? #'a #'c) (type=? #'b #'d))]
    [[(#%type:forall x a) (#%type:forall y b)] (and (free-identifier=? #'x #'y) (type=? #'a #'b))]
    [[_ _] #f]))

; Determines if a type is monomorphic, which simply checks if the type contains any quantifiers.
(define/contract type-mono?
  (-> type? boolean?)
  (syntax-parser
    #:context 'type-mono?
    #:literal-sets [type-literals]
    [_:id #t]
    [(#%type:wobbly-var _) #t]
    [(#%type:rigid-var _) #t]
    [(#%type:con _) #t]
    [(#%type:app a b) (and (type-mono? #'a) (type-mono? #'b))]
    [(#%type:forall _ _) #f]
    [(#%type:qual a b) (and (type-mono? #'a) (type-mono? #'b))]))

; Returns all solver variables present in a type.
(define/contract type-vars^
  (-> type? (listof identifier?))
  (syntax-parser
    #:context 'type-vars^
    #:literal-sets [type-literals]
    [_:id '()]
    [(#%type:wobbly-var x) (list #'x)]
    [(#%type:rigid-var _) '()]
    [(#%type:con _) '()]
    [(#%type:app a b)
     (remove-duplicates (append (type-vars^ #'a) (type-vars^ #'b)) free-identifier=?)]
    [(#%type:forall _ t) (type-vars^ #'t)]
    [(#%type:qual a b)
     (remove-duplicates (append (type-vars^ #'a) (type-vars^ #'b)) free-identifier=?)]))

(define/contract (type->string t)
  (-> type? string?)
  (~a (type->datum t)))

(define/contract type->datum
  (-> type? any/c)
  (syntax-parser
    #:context 'type->string
    #:literal-sets [type-literals]
    [x:id (syntax-e #'x)]
    [(#%type:wobbly-var x^) (string->symbol (format "~a^" (syntax-e #'x^)))]
    [(#%type:rigid-var x^) (syntax-e #'x^)]
    [(#%type:con name) (syntax-e #'name)]
    [{~#%type:app+ (#%type:con {~var op (infix-operator #:default-fixity #f)}) _ _}
     (infix-type->string #'op (attribute op.fixity) this-syntax)]
    [{~#%type:app+ t ...} (map type->datum (attribute t))]
    [{~#%type:forall* [x ...+] {~#%type:qual* [constr ...+] t}}
     `(forall ,(map syntax-e (attribute x))
              ,@(map type->datum (attribute constr))
              => ,(type->datum #'t))]
    [{~#%type:forall* [x ...+] t}
     `(forall ,(map syntax-e (attribute x)) ,(type->datum #'t))]
    [{~#%type:qual* [constr ...+] t}
     `(=> ,(map type->datum (attribute constr)) ,(type->datum #'t))]))

(define/contract (infix-type->string op-id fixity t0)
  (-> identifier? operator-fixity? type? string?)
  (define traverse
    (syntax-parser
      #:literal-sets [type-literals]
      [{~#%type:app* (#%type:con op) t s}
       #:when (free-identifier=? #'op op-id)
       (case fixity
         [(left)  (snoc (traverse #'t) #'s)]
         [(right) (cons #'t (traverse #'s))])]
      [t (list #'t)]))
  (string-join (map type->string (traverse t0))
               (format " ~a " (syntax-e op-id))
               #:before-first "{"
               #:after-last "}"))

;; ---------------------------------------------------------------------------------------------------
;; type contexts

(struct ctx:solution (x^ t) #:prefab)

(define (ctx-elem? x) ((disjoin ctx:solution?) x))
(define (ctx? x) ((listof ctx-elem?) x))
(define/contract ctx-elem=?
  (-> ctx-elem? ctx-elem? boolean?)
  (match-lambda**
   [[(ctx:solution x^ a) (ctx:solution y^ b)] (and (free-identifier=? x^ y^) (type=? a b))]
   [[_ _] #f]))
(define/contract (ctx-member? ctx elem)
  (-> ctx? ctx-elem? boolean?)
  (and (member elem ctx ctx-elem=?) #t))
(define/contract (ctx-remove ctx elem)
  (-> ctx? ctx-elem? ctx?)
  (remove elem ctx ctx-elem=?))

(define/contract (ctx-find-solution ctx x^)
  (-> ctx? identifier? (or/c type? #f))
  (and~> (findf #{and (ctx:solution? %) (free-identifier=? x^ (ctx:solution-x^ %))} ctx)
         ctx:solution-t))
(define/contract (current-ctx-solution x^)
  (-> identifier? (or/c type? #f))
  (ctx-find-solution (current-type-context) x^))

(define/contract (apply-subst ctx t)
  (-> ctx? type? type?)
  (syntax-parse t
    #:context 'apply-subst
    #:literal-sets [type-literals]
    [_:id t]
    [(#%type:wobbly-var x) (let ([s (ctx-find-solution ctx #'x)])
                             (if s (apply-subst ctx s) t))]
    [(#%type:rigid-var _) t]
    [(#%type:con _) t]
    [(head:#%type:app a b) (quasisyntax/loc/props this-syntax
                             (head #,(apply-subst ctx #'a) #,(apply-subst ctx #'b)))]
    [(head:#%type:forall x t) (quasisyntax/loc/props this-syntax
                                (head x #,(apply-subst ctx #'t)))]
    [(head:#%type:qual a b) (quasisyntax/loc/props this-syntax
                              (head #,(apply-subst ctx #'a) #,(apply-subst ctx #'b)))]))
(define (apply-current-subst t)
  (apply-subst (current-type-context) t))

(define/contract (generalize t)
  (-> type? type?)
  (let* ([xs^ (type-vars^ t)]
         [xs (generate-temporaries xs^)]
         [subst (map ctx:solution xs^ xs)])
    (expand-type (quasitemplate (?#%type:forall* #,xs #,(apply-subst subst t))))))

(define/contract (inst t x s)
  (-> type? identifier? type? type?)
  (insts t (list (cons x s))))

(define/contract (insts t x+ss)
  (-> type? (listof (cons/c identifier? type?)) type?)
  (let ([intdef-ctx (with-handlers ([exn:fail? (λ (e)
                                                 (println (syntax-local-context))
                                                 (raise e))])
                      (syntax-local-make-definition-context))])
    (for ([x+s (in-list x+ss)])
      (syntax-local-bind-syntaxes (list (car x+s))
                                  #`(make-variable-like-transformer (quote-syntax #,(cdr x+s)))
                                  intdef-ctx))
    (expand-type t intdef-ctx)))

(define/contract current-type-context (parameter/c ctx?) (make-parameter '()))
(define/contract (modify-type-context f)
  (-> (-> ctx? ctx?) void?)
  (current-type-context (f (current-type-context))))

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
;; subsumption, instantiation, and elaboration

(define/contract (type<:/full! a b #:src src #:elaborate? elaborate?)
  (->i ([a type?]
        [b type?]
        #:src [src syntax?]
        #:elaborate? [elaborate? boolean?])
       [result (elaborate?) (if elaborate? (listof constr?) void?)])
  (define no-op (if elaborate? '() (void)))
  (syntax-parse (list (apply-current-subst a) (apply-current-subst b))
    #:context 'type<:/full!
    #:literal-sets [type-literals]
    ; <:Con
    [[(#%type:con a) (#%type:con b)]
     #:when (free-identifier=? #'a #'b)
     no-op]
    ; <:Var
    [[x:id y:id]
     #:when (free-identifier=? #'x #'y)
     no-op]
    ; <:Exvar
    [[(#%type:wobbly-var x^) (#%type:wobbly-var y^)]
     #:when (free-identifier=? #'x^ #'y^)
     no-op]
    [[(#%type:rigid-var x^) (#%type:rigid-var y^)]
     #:when (free-identifier=? #'x^ #'y^)
     no-op]
    ; <:→
    ; we need to handle → specially since it is allowed to be applied to polytypes
    [[(~-> a b) (~-> c d)]
     (type<:! #'c #'a #:src src)
     (type<:! #'b #'d #:src src)
     no-op]
    ; <:App
    [[(#%type:app a b) (#%type:app c d)]
     (for ([t (in-list (list #'a #'b #'c #'d))])
       (unless (type-mono? t)
         (raise-syntax-error #f (~a "illegal polymorphic type " (type->string t)
                                    ", impredicative polymorphism is not supported") src)))
     (type<:! #'a #'c #:src src)
     (type<:! #'b #'d #:src src)
     no-op]
    ; <:∀L
    [[(#%type:forall x a) b]
     (let ([a* (inst #'a #'x #`(#%type:wobbly-var #,(generate-temporary #'x)))])
       (type<:/full! a* #'b #:src src #:elaborate? elaborate?))]
    ; <:∀R
    [[a (#%type:forall x b)]
     (let* ([x^ (generate-temporary #'x)]
            [b* (inst #'b #'x #`(#%type:rigid-var #,x^))])
       (type<:/full! #'a b* #:src src #:elaborate? elaborate?))]
    ; <:Qual
    [[(#%type:qual constr a) b]
     #:when elaborate?
     (snoc (type<:/elaborate! #'a #'b #:src src) #'constr)]
    ; <:InstantiateL
    [[(#%type:wobbly-var x^) a]
     #:when (not (member #'x^ (type-vars^ #'a) free-identifier=?))
     (type-inst-l! #'x^ #'a)
     no-op]
    ; <:InstantiateR
    [[a (#%type:wobbly-var x^)]
     #:when (not (member #'x^ (type-vars^ #'a) free-identifier=?))
     (type-inst-r! #'a #'x^)
     no-op]
    [[a b]
     (raise-syntax-error 'typechecker
                         (~a "type mismatch\n"
                             "  between: " (type->string #'a) "\n"
                             "      and: " (type->string #'b))
                         src)]))

(define/contract (type<:/elaborate! a b #:src src)
  (-> type? type? #:src syntax? (listof constr?))
  (type<:/full! a b #:src src #:elaborate? #t))

(define/contract (type<:! a b #:src src)
  (-> type? type? #:src syntax? void?)
  (type<:/full! a b #:src src #:elaborate? #f))

(define/contract (type-inst-l! x^ t)
  (-> identifier? type? void?)
  (syntax-parse t
    #:context 'type-inst-l!
    #:literal-sets [type-literals]
    ; InstLSolve
    [_
     #:when (type-mono? t)
     (modify-type-context #{snoc % (ctx:solution x^ t)})]
    ; InstLArr
    [(~-> a b)
     #:with [x1^ x2^] (generate-temporaries (list x^ x^))
     (modify-type-context
      #{snoc % (ctx:solution x^ (template (?->* (#%type:wobbly-var x1^) (#%type:wobbly-var x2^))))})
     (type-inst-r! #'a #'x1^)
     (type-inst-l! #'x2^ (apply-current-subst #'b))]
    ; InstLAllR
    [(#%type:forall x t*)
     (type-inst-l! x^ #'t*)]
    [_ (error 'type-inst-l! (format "internal error: failed to instantiate ~a to a subtype of ~a"
                                 (type->string #`(#%type:wobbly-var #,x^)) (type->string t)))]))

(define/contract (type-inst-r! t x^)
  (-> type? identifier? void?)
  (syntax-parse t
    #:context 'type-inst-r!
    #:literal-sets [type-literals]
    ; InstRSolve
    [_
     #:when (type-mono? t)
     (modify-type-context #{snoc % (ctx:solution x^ t)})]
    ; InstRArr
    [(~-> a b)
     #:with [x1^ x2^] (generate-temporaries (list x^ x^))
     (modify-type-context
      #{snoc % (ctx:solution x^ (template (?->* (#%type:wobbly-var x1^) (#%type:wobbly-var x2^))))})
     (type-inst-l! #'x1^ #'a)
     (type-inst-r! (apply-current-subst #'b) #'x2^)]
    ; InstRAllL
    [(#%type:forall x t*)
     #:with y^ (generate-temporary #'x)
     (type-inst-r! (inst #'t* #'x #'(#%type:wobbly-var y^)) x^)]
    [_ (error 'type-inst-r! (format "internal error: failed to instantiate ~a to a supertype of ~a"
                                 (type->string #`(#%type:wobbly-var #,x^)) (type->string t)))]))

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
     (modify-type-context #{snoc % (ctx:solution #'x^ #'t)})
     #t]
    [[(#%type:con a) (#%type:con b)]
     #:when (free-identifier=? #'a #'b)
     #t]
    [[(#%type:app a b) (#%type:app c d)]
     (and (types-match?! #'a #'c) (types-match?! #'b #'d))]
    [[_ _]
     #f]))

;; ---------------------------------------------------------------------------------------------------

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

;; -------------------------------------------------------------------------------------------------

; To support type tooltips, we attach 'mouse-over-tooltips properties to syntax objects whenever we
; attach a type, unless the 'omit-type-tooltip property is already present. When we attach these
; tooltips, we might not know the fully-solved type yet, so we perform a second pass after the module
; is fully-expanded that applies the current substitution whenever it sees a type. It’s important to
; apply this substitution while the module is still being expanded, since otherwise, the type context
; will be empty!
;
; To support this, we wrap the type inside a deferred-type-in-tooltip struct. This struct cooperates
; with the 'mouse-over-tooltips property by being a procedure, so even if we somehow fail to discover
; the property and evaluate it earlier, we’ll at least get *some* information. When
; apply-current-subst-in-tooltips is called, however, we evaluate the thunk early and replace the
; property with the new value, improving the information in the tooltips.

(struct deferred-type-in-tooltip (type)
  #:property prop:procedure
  (λ (self) (type->string (apply-current-subst (deferred-type-in-tooltip-type self)))))

(define/contract (attach-type stx t #:tooltip-src [tooltip-src stx])
  (->* [syntax? type?] [#:tooltip-src any/c] syntax?)
  (let ([stx* (syntax-property stx ': t)])
    (if (and (not (syntax-property tooltip-src 'omit-type-tooltip))
             (syntax-source tooltip-src)
             (syntax-position tooltip-src)
             (syntax-span tooltip-src))
        (syntax-property
         stx* 'mouse-over-tooltips
         (syntax-parse tooltip-src
           ; If it’s a pair, just add the tooltip “on the parens”.
           [(_ . _)
            (cons
             (vector tooltip-src
                     (sub1 (syntax-position tooltip-src))
                     (syntax-position tooltip-src)
                     (deferred-type-in-tooltip t))
             (vector tooltip-src
                     (+ (sub1 (syntax-position tooltip-src)) (sub1 (syntax-span tooltip-src)))
                     (+ (sub1 (syntax-position tooltip-src)) (syntax-span tooltip-src))
                     (deferred-type-in-tooltip t)))]
           ; Otherwise, add the tooltip on the whole region.
           [_
            (vector tooltip-src
                    (sub1 (syntax-position tooltip-src))
                    (+ (sub1 (syntax-position tooltip-src)) (syntax-span tooltip-src))
                    (deferred-type-in-tooltip t))]))
        stx*)))
(define/contract (attach-expected stx t)
  (-> syntax? type? syntax?)
  (syntax-property stx ':⇐ t))

(define/contract (get-type stx)
  (-> syntax? (or/c type? #f))
  (let loop ([val (syntax-property stx ':)])
    (if (pair? val) (loop (car val)) val)))
(define/contract (get-expected stx)
  (-> syntax? (or/c type? #f))
  (let loop ([val (syntax-property stx ':⇐)])
    (if (pair? val) (loop (car val)) val)))

(define (apply-current-subst-in-tooltips stx)
  (recursively-adjust-property
   stx 'mouse-over-tooltips
   (match-lambda
     [(vector a b c (? deferred-type-in-tooltip? d))
      (vector a b c (d))]
     [other other])))

(define/contract (make-typed-var-transformer x t)
  (-> identifier? type? any)
  (make-variable-like-transformer
   ; Adjust source location information before calling attach-type so that tooltips end up in the
   ; right place.
   (λ (stx) (attach-type (replace-stx-loc x stx) t))))
