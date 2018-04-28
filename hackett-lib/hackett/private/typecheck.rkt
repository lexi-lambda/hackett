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
                       hackett/private/type-language)
         (for-syntax racket/base
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
         syntax/parse/define
         syntax/parse/experimental/template
         threading

         hackett/private/util/list
         hackett/private/util/stx)

(provide (contract-out [struct ctx:var ([x identifier?])]
                       [struct ctx:rigid ([x^ identifier?])]
                       [struct ctx:solution ([x^ identifier?] [t type?])]
                       [struct class:info ([vars (listof identifier?)]
                                           [method-table immutable-free-id-table?]
                                           [default-methods immutable-free-id-table?]
                                           [superclasses (listof constr?)]
                                           [deriving-transformer (or/c (-> syntax? syntax?) #f)])]
                       [struct class:instance ([class class:info?]
                                               [vars (listof identifier?)]
                                               [subgoals (listof constr?)]
                                               [ts (listof (and/c type? τ-mono?))]
                                               [dict-expr syntax?])])
         type? τ=? constr? τ-mono? τ-vars^ τ->string τ-wf! current-τ-wf!
         generalize inst insts τ<:/full! τ<:/elaborate! τ<:! τ-inst-l! τ-inst-r!
         ctx-elem? ctx? ctx-elem=? ctx-member? ctx-remove
         ctx-find-solution current-ctx-solution apply-subst apply-current-subst
         current-type-context modify-type-context
         register-global-class-instance! lookup-instance!
         expand-type attach-type attach-expected get-type get-expected make-typed-var-transformer

         (for-template (all-from-out hackett/private/type-language)
                       local-class-instances))

;; ---------------------------------------------------------------------------------------------------
;; type operations

(define (type? x) (syntax? x))
(define (constr? x) (type? x))

; Compares two types for literal equality. This is a much more primitive notion than type
; “equivalence”, since it does not check alpha-equivalence. This means that (forall [a] a) and
; (forall [b] b) will be considered different types.
(define/contract (τ=? a b)
  (-> type? type? boolean?)
  (syntax-parse (list a b)
    #:context 'τ=?
    #:literal-sets [type-literals]
    [[(#%type:bound-var x) (#%type:bound-var y)] (free-identifier=? #'x #'y)]
    [[(#%type:wobbly-var x) (#%type:wobbly-var y)] (free-identifier=? #'x #'y)]
    [[(#%type:rigid-var x) (#%type:rigid-var y)] (free-identifier=? #'x #'y)]
    [[(#%type:con a) (#%type:con b)] (free-identifier=? #'a #'b)]
    [[(#%type:app a b) (#%type:app c d)] (and (τ=? #'a #'c) (τ=? #'b #'d))]
    [[(#%type:forall x a) (#%type:forall y b)] (and (free-identifier=? #'x #'y) (τ=? #'a #'b))]
    [[_ _] #f]))

; Determines if a type is monomorphic, which simply checks if the type contains any quantifiers.
(define/contract τ-mono?
  (-> type? boolean?)
  (syntax-parser
    #:context 'τ-mono?
    #:literal-sets [type-literals]
    [(#%type:bound-var _) #t]
    [(#%type:wobbly-var _) #t]
    [(#%type:rigid-var _) #t]
    [(#%type:con _) #t]
    [(#%type:app a b) (and (τ-mono? #'a) (τ-mono? #'b))]
    [(#%type:forall _ _) #f]
    [(#%type:qual a b) (and (τ-mono? #'a) (τ-mono? #'b))]))

; Returns all solver variables present in a type.
(define/contract τ-vars^
  (-> type? (listof identifier?))
  (syntax-parser
    #:context 'τ-vars^
    #:literal-sets [type-literals]
    [(#%type:bound-var _) '()]
    [(#%type:wobbly-var x) (list #'x)]
    [(#%type:rigid-var _) '()]
    [(#%type:con _) '()]
    [(#%type:app a b) (remove-duplicates (append (τ-vars^ #'a) (τ-vars^ #'b)) free-identifier=?)]
    [(#%type:forall _ t) (τ-vars^ #'t)]
    [(#%type:qual a b)
     (remove-duplicates (append (τ-vars^ #'a) (τ-vars^ #'b)) free-identifier=?)]))

(define/contract (τ->string t)
  (-> type? string?)
  (format "~a" (τ->datum t)))

(define/contract τ->datum
  (-> type? any/c)
  (syntax-parser
    #:context 'τ->datum
    #:literal-sets [type-literals]
    [(#%type:bound-var x) (syntax-e #'x)]
    [(#%type:wobbly-var x^) (string->symbol (format "~a^" (syntax-e #'x^)))]
    [(#%type:rigid-var x^) (syntax-e #'x^)]
    [(#%type:con name) (syntax-e #'name)]
    [{~#%type:app+ t ...} (map τ->datum (attribute t))]
    [{~#%type:forall* [x ...+] {~#%type:qual* [constr ...+] t}}
     `(forall ,(map syntax-e (attribute x))
              ,@(map τ->datum (attribute constr))
              => ,(τ->datum #'t))]
    [{~#%type:forall* [x ...+] t}
     `(forall ,(map syntax-e (attribute x)) ,(τ->datum #'t))]
    [{~#%type:qual* [constr ...+] t}
     `(=> ,(map τ->datum (attribute constr)) ,(τ->datum #'t))]))

;; ---------------------------------------------------------------------------------------------------
;; type contexts

(struct ctx:var (x) #:prefab)
(struct ctx:rigid (x^) #:prefab)
(struct ctx:solution (x^ t) #:prefab)

(define (ctx-elem? x) ((disjoin ctx:var? ctx:rigid? ctx:solution?) x))
(define (ctx? x) ((listof ctx-elem?) x))
(define/contract ctx-elem=?
  (-> ctx-elem? ctx-elem? boolean?)
  (match-lambda**
   [[(ctx:var x) (ctx:var y)] (free-identifier=? x y)]
   [[(ctx:rigid x^) (ctx:rigid y^)] (free-identifier=? x^ y^)]
   [[(ctx:solution x^ a) (ctx:solution y^ b)] (and (free-identifier=? x^ y^) (τ=? a b))]
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

(define/contract (τ-wf! ctx t)
  (-> ctx? type? void?)
  (syntax-parse t
    #:context 'τ-wf!
    #:literal-sets [type-literals]
    [(#%type:bound-var ~! x:id) (unless (ctx-member? ctx (ctx:var #'x))
                                  (raise-syntax-error #f "unbound type variable" #'x))]
    [(#%type:wobbly-var ~! _:id) (void)]
    [(#%type:rigid-var ~! x^:id) (unless (ctx-member? ctx (ctx:rigid #'x^))
                                   (raise-syntax-error #f "skolem escaped its scope" #'x^))]
    [(#%type:con ~! _:id) (void)]
    [(#%type:app ~! a b) (τ-wf! ctx #'a) (τ-wf! ctx #'b)]
    [(#%type:forall ~! x:id t) (τ-wf! (snoc ctx (ctx:var #'x)) #'t)]
    [(#%type:qual ~! a b) (τ-wf! ctx #'a) (τ-wf! ctx #'b)]))
(define/contract (current-τ-wf! t)
  (-> type? void?)
  (τ-wf! (current-type-context) t))

(define/contract (apply-subst ctx t)
  (-> ctx? type? type?)
  (syntax-parse t
    #:context 'apply-subst
    #:literal-sets [type-literals]
    [(#%type:bound-var _) t]
    [(#%type:wobbly-var x) (let ([s (ctx-find-solution ctx #'x)])
                             (if s (apply-subst ctx s) t))]
    [(#%type:rigid-var _) t]
    [(#%type:con _) t]
    [(head:#%type:app a b) (quasisyntax/loc/props this-syntax
                             (#%type:app #,(apply-subst ctx #'a) #,(apply-subst ctx #'b)))]
    [(head:#%type:forall x t) (quasisyntax/loc/props this-syntax
                                (head x #,(apply-subst ctx #'t)))]
    [(head:#%type:qual a b) (quasisyntax/loc/props this-syntax
                              (head #,(apply-subst ctx #'a) #,(apply-subst ctx #'b)))]))
(define (apply-current-subst t)
  (apply-subst (current-type-context) t))

(define/contract (generalize t)
  (-> type? type?)
  (let* ([xs^ (τ-vars^ t)]
         [xs (generate-temporaries xs^)]
         [subst (map #{ctx:solution %1 #`(#%type:bound-var #,%2)} xs^ xs)])
    (quasitemplate (?#%type:forall* #,xs #,(apply-subst subst t)))))

(define/contract (inst t x s)
  (-> type? identifier? type? type?)
  (syntax-parse t
    #:context 'inst
    #:literal-sets [type-literals]
    [(#%type:bound-var y) (if (free-identifier=? x #'y) s t)]
    [(#%type:wobbly-var _) t]
    [(#%type:rigid-var _) t]
    [(#%type:con _) t]
    [(head:#%type:app a b)
     (quasisyntax/loc/props this-syntax
       (head #,(inst #'a x s) #,(inst #'b x s)))]
    [(head:#%type:forall v t*)
     (quasisyntax/loc/props this-syntax
       (head v #,(inst #'t* x s)))]
    [(head:#%type:qual a b)
     (quasisyntax/loc/props this-syntax
       (head #,(inst #'a x s) #,(inst #'b x s)))]
    [_ t]))

(define/contract (insts t x+ss)
  (-> type? (listof (cons/c identifier? type?)) type?)
  (foldl #{inst %2 (car %1) (cdr %1)} t x+ss))

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

(define/contract (τ<:/full! a b #:src src #:elaborate? elaborate?)
  (->i ([a type?]
        [b type?]
        #:src [src syntax?]
        #:elaborate? [elaborate? boolean?])
       [result (elaborate?) (if elaborate? (listof constr?) void?)])
  (define no-op (if elaborate? '() (void)))
  (syntax-parse (list (apply-current-subst a) (apply-current-subst b))
    #:context 'τ<:/full!
    #:literal-sets [type-literals]
    ; <:Con
    [[(#%type:con a) (#%type:con b)]
     #:when (free-identifier=? #'a #'b)
     no-op]
    ; <:Var
    [[(#%type:bound-var x) (#%type:bound-var y)]
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
     (τ<:! #'c #'a #:src src)
     (τ<:! #'b #'d #:src src)
     no-op]
    ; <:App
    [[(#%type:app a b) (#%type:app c d)]
     (for ([t (in-list (list #'a #'b #'c #'d))])
       (unless (τ-mono? t)
         (raise-syntax-error #f (~a "illegal polymorphic type " (τ->string t)
                                    ", impredicative polymorphism is not supported") src)))
     (τ<:! #'a #'c #:src src)
     (τ<:! #'b #'d #:src src)
     no-op]
    ; <:∀L
    [[(#%type:forall x a) b]
     (let ([a* (inst #'a #'x #`(#%type:wobbly-var #,(generate-temporary #'x)))])
       (τ<:/full! a* #'b #:src src #:elaborate? elaborate?))]
    ; <:∀R
    [[a (#%type:forall x b)]
     (let* ([x^ (generate-temporary #'x)]
            [b* (inst #'b #'x #`(#%type:rigid-var #,x^))])
       (modify-type-context #{snoc % (ctx:rigid x^)})
       (begin0
         (τ<:/full! #'a b* #:src src #:elaborate? elaborate?)
         (modify-type-context #{ctx-remove % (ctx:rigid x^)})))]
    ; <:Qual
    [[(#%type:qual constr a) b]
     #:when elaborate?
     (snoc (τ<:/elaborate! #'a #'b #:src src) #'constr)]
    ; <:InstantiateL
    [[(#%type:wobbly-var x^) a]
     #:when (not (member #'x^ (τ-vars^ #'a) free-identifier=?))
     (τ-inst-l! #'x^ #'a)
     no-op]
    ; <:InstantiateR
    [[a (#%type:wobbly-var x^)]
     #:when (not (member #'x^ (τ-vars^ #'a) free-identifier=?))
     (τ-inst-r! #'a #'x^)
     no-op]
    [[a b]
     (raise-syntax-error 'typechecker
                         (~a "type mismatch\n"
                             "  between: " (τ->string #'a) "\n"
                             "      and: " (τ->string #'b))
                         src)]))

(define/contract (τ<:/elaborate! a b #:src src)
  (-> type? type? #:src syntax? (listof constr?))
  (τ<:/full! a b #:src src #:elaborate? #t))

(define/contract (τ<:! a b #:src src)
  (-> type? type? #:src syntax? void?)
  (τ<:/full! a b #:src src #:elaborate? #f))

(define/contract (τ-inst-l! x^ t)
  (-> identifier? type? void?)
  (syntax-parse t
    #:context 'τ-inst-l!
    #:literal-sets [type-literals]
    ; InstLSolve
    [_
     #:when (τ-mono? t)
     (modify-type-context #{snoc % (ctx:solution x^ t)})]
    ; InstLArr
    [(~-> a b)
     #:with [x1^ x2^] (generate-temporaries (list x^ x^))
     (modify-type-context
      #{snoc % (ctx:solution x^ (template (?->* (#%type:wobbly-var x1^) (#%type:wobbly-var x2^))))})
     (τ-inst-r! #'a #'x1^)
     (τ-inst-l! #'x2^ (apply-current-subst #'b))]
    ; InstLAllR
    [(#%type:forall x t*)
     (modify-type-context #{snoc % (ctx:var #'x)})
     (τ-inst-l! x^ #'t*)
     (modify-type-context #{ctx-remove % (ctx:var #'x)})]
    [_ (error 'τ-inst-l! (format "internal error: failed to instantiate ~a to a subtype of ~a"
                                 (τ->string #`(#%type:wobbly-var #,x^)) (τ->string t)))]))

(define/contract (τ-inst-r! t x^)
  (-> type? identifier? void?)
  (syntax-parse t
    #:context 'τ-inst-r!
    #:literal-sets [type-literals]
    ; InstRSolve
    [_
     #:when (τ-mono? t)
     (modify-type-context #{snoc % (ctx:solution x^ t)})]
    ; InstRArr
    [(~-> a b)
     #:with [x1^ x2^] (generate-temporaries (list x^ x^))
     (modify-type-context
      #{snoc % (ctx:solution x^ (template (?->* (#%type:wobbly-var x1^) (#%type:wobbly-var x2^))))})
     (τ-inst-l! #'x1^ #'a)
     (τ-inst-r! (apply-current-subst #'b) #'x2^)]
    ; InstRAllL
    [(#%type:forall x t*)
     #:with y^ (generate-temporary #'x)
     (τ-inst-r! (inst #'t* #'x #'(#%type:wobbly-var y^)) x^)]
    [_ (error 'τ-inst-r! (format "internal error: failed to instantiate ~a to a supertype of ~a"
                                 (τ->string #`(#%type:wobbly-var #,x^)) (τ->string t)))]))

;; ---------------------------------------------------------------------------------------------------

; Attempts to unify a type with an instance head with a type for the purposes of picking a typeclass.
; If the match succeeds, it returns a list of instantiated subgoals for the instance, otherwise it
; returns #f.
(define/contract (unify-instance-head ts vars subgoals head)
  (-> (listof type?) (listof identifier?) (listof constr?) (listof (and/c type? τ-mono?))
      (or/c (listof constr?) #f))
  (let* ([vars^ (generate-temporaries vars)]
         [var-subst (map #{cons %1 #`(#%type:wobbly-var #,%2)} vars vars^)]
         [head-inst (map #{insts % var-subst} head)]
         [subgoals-inst (map #{insts % var-subst} subgoals)])
    (and (for/and ([t (in-list ts)]
                   [head-t (in-list head-inst)])
           (let loop ([t t]
                      [head-t head-t])
             (syntax-parse (list (apply-current-subst t) (apply-current-subst head-t))
               #:context 'unify-instance-head
               #:literal-sets [type-literals]
               [[(#%type:rigid-var x^) (#%type:rigid-var y^)]
                #:when (free-identifier=? #'x^ #'y^)
                #t]
               [[t (#%type:wobbly-var x^)]
                #:when (τ-mono? #'t)
                (modify-type-context #{snoc % (ctx:solution #'x^ #'t)})
                #t]
               [[(#%type:con a) (#%type:con b)]
                #:when (free-identifier=? #'a #'b)
                #t]
               [[(#%type:app a b) (#%type:app c d)]
                (and (loop #'a #'c) (loop #'b #'d))]
               [[_ _]
                #f])))
         subgoals-inst)))

(define/contract (lookup-instance! constr #:src src)
  (-> constr? #:src syntax? (values class:instance? (listof constr?)))
  (define/syntax-parse (~#%type:app* ({~literal #%type:con} class-id) ts ...) constr)
  (define ts* (map apply-current-subst (attribute ts)))
  (define class (syntax-local-value #'class-id)) ; FIXME: handle when this isn’t a class:info
  (apply values
         (or (for/or ([instance (in-list (current-instances-of-class class))])
               (let ([old-type-context (current-type-context)])
                 (let ([constrs (unify-instance-head ts*
                                                     (class:instance-vars instance)
                                                     (class:instance-subgoals instance)
                                                     (class:instance-ts instance))])
                   (if constrs (list instance constrs)
                       (begin (current-type-context old-type-context) #f)))))
             (raise-syntax-error 'typechecker
                                 (~a "could not deduce " (τ->string (apply-current-subst constr)))
                                 src))))

;; -------------------------------------------------------------------------------------------------

(define/contract (attach-type stx t)
  (-> syntax? type? syntax?)
  (syntax-property stx ': t))
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

(define/contract (make-typed-var-transformer x t)
  (-> identifier? type? any)
  (make-variable-like-transformer (attach-type x t)))
