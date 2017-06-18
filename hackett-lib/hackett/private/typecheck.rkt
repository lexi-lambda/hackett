#lang curly-fn racket/base

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
                       [struct ctx:var^ ([x^ identifier?])]
                       [struct ctx:skolem ([x^ identifier?])]
                       [struct ctx:assump ([x identifier?] [t τ?])]
                       [struct ctx:solution ([x^ identifier?] [t τ?])]
                       [struct class:info ([var identifier?]
                                           [method-table immutable-free-id-table?]
                                           [superclasses (listof constr?)])]
                       [struct class:instance ([class class:info?] [t τ?] [dict-expr syntax?])])
         τ? τ:-> τ:->? τ:->* τ=? constr? τ-mono? τ-vars^ τ->string τ-wf! current-τ-wf!
         generalize inst τ<:/full! τ<:/elaborate! τ<:! τ-inst-l! τ-inst-r!
         ctx-elem? ctx? ctx-elem=? ctx-member? ctx-remove
         ctx-find-solution current-ctx-solution apply-subst apply-current-subst
         current-type-context modify-type-context
         register-global-class-instance! local-class-instances lookup-instance!
         type type-transforming? parse-type τ-stx-token local-expand-type
         make-type-variable-transformer attach-type attach-expected get-type get-expected
         make-typed-var-transformer)

(struct τ:var (x) #:prefab)
(struct τ:var^ (x^) #:prefab)
(struct τ:skolem (x^) #:prefab)
(struct τ:con (name constructors) #:prefab)
(struct τ:app (a b) #:prefab)
(struct τ:∀ (x t) #:prefab)
(struct τ:qual (constr t) #:prefab)

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

(define (τ? x) ((disjoin τ:var? τ:var^? τ:skolem? τ:con? τ:app? τ:∀? τ:qual?) x))
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

(struct ctx:var (x) #:prefab)
(struct ctx:var^ (x^) #:prefab)
(struct ctx:skolem (x^) #:prefab)
(struct ctx:assump (x t) #:prefab)
(struct ctx:solution (x^ t) #:prefab)

(define (ctx-elem? x) ((disjoin ctx:var? ctx:var^? ctx:skolem? ctx:assump? ctx:solution?) x))
(define (ctx? x) ((listof ctx-elem?) x))
(define/contract ctx-elem=?
  (-> ctx-elem? ctx-elem? boolean?)
  (match-lambda**
   [[(ctx:var x) (ctx:var y)] (free-identifier=? x y)]
   [[(ctx:var^ x) (ctx:var^ y)] (free-identifier=? x y)]
   [[(ctx:skolem x^) (ctx:skolem y^)] (free-identifier=? x^ y^)]
   [[(ctx:assump x a) (ctx:assump y b)] (and (free-identifier=? x y) (τ=? a b))]
   [[(ctx:solution x^ a) (ctx:solution y^ b)] (and (free-identifier=? x^ y^) (τ=? a b))]
   [[_ _] #f]))
(define/contract (ctx-member? ctx elem)
  (-> ctx? ctx-elem? boolean?)
  (and (member elem ctx ctx-elem=?) #t))
(define/contract (ctx-remove ctx elem)
  (-> ctx? ctx-elem? ctx?)
  (remove elem ctx ctx-elem=?))

(define (ctx-find-assump ctx x)
  (and~> (findf #{and (ctx:assump? %) (free-identifier=? x (ctx:assump-x %))} ctx)
         ctx:assump-t))
(define (current-ctx-assump x)
  (ctx-find-assump (current-type-context) x))

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
    [(τ:var^ x^) (unless (or (ctx-member? ctx (ctx:var^ x^))
                             (ctx-find-solution ctx x^))
                   (raise-syntax-error #f "unbound existential variable" x^))]
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

(define/contract current-type-context (parameter/c ctx?) (make-parameter '()))
(define/contract (modify-type-context f)
  (-> (-> ctx? ctx?) void?)
  (current-type-context (f (current-type-context))))

(struct class:info (var method-table superclasses) #:transparent
  #:property prop:procedure
  (λ (info stx)
    ((make-type-variable-transformer
      (τ:con (syntax-parse stx
               [id:id #'id]
               [(id:id . _) #'id])
             #f))
     stx)))
(struct class:instance (class t dict-expr) #:transparent)

(define global-class-instances (make-gvector))
(define/contract (register-global-class-instance! instance)
  (-> class:instance? void?)
  (gvector-add! global-class-instances instance))
(define/contract local-class-instances (parameter/c (listof class:instance?)) (make-parameter '()))
(define/contract (current-class-instances)
  (-> (listof class:instance?))
  (append (gvector->list global-class-instances)
          (local-class-instances)))

(define (current-instances-of-class class)
  (-> class:info? (listof class:instance?))
  (filter #{eq? class (class:instance-class %)} (current-class-instances)))

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
       (modify-type-context #{snoc % (ctx:var^ x^)})
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
       (modify-type-context #{append % (list (ctx:var^ x2^) (ctx:var^ x1^) (ctx:solution x^ (τ:->* (τ:var^ x1^) (τ:var^ x2^))))})
       (τ-inst-r! a x1^)
       (τ-inst-l! x2^ (apply-current-subst b)))]
    ; InstLAllR
    [(τ:∀ x t*)
     (modify-type-context #{snoc % (ctx:var x)})
     (τ-inst-l! x^ t*)
     (modify-type-context #{ctx-remove % (ctx:var x)})]
    [_ (error 'τ-inst-l! (format "failed to instantiate ~a to a subtype of ~a"
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
       (modify-type-context #{append % (list (ctx:var^ x2^) (ctx:var^ x1^) (ctx:solution x^ (τ:->* (τ:var^ x1^) (τ:var^ x2^))))})
       (τ-inst-l! x1^ a)
       (τ-inst-r! (apply-current-subst b) x2^))]
    ; InstRAllL
    [(τ:∀ x t*)
     (let ([y^ (generate-temporary x)])
       (modify-type-context #{snoc % (ctx:var^ y^)})
       (τ-inst-r! (inst t* x (τ:var^ y^)) x^)
       (modify-type-context #{ctx-remove % (ctx:var^ y^)}))]
    [_ (error 'τ-inst-r! (format "failed to instantiate ~a to a supertype of ~a"
                                 (τ->string (τ:var^ x^)) (τ->string t)))]))

;; ---------------------------------------------------------------------------------------------------

; Attempts to unify a type with an instance head with a type for the purposes of picking a typeclass.
; If the match succeeds, it returns a list of constraints, which are the subgoals for the instance,
; if any.
(define/contract (unify-instance-head t head)
  (-> τ? τ? (or/c (listof constr?) #f))
  (match* [(apply-current-subst t) (apply-current-subst head)]
    [[(τ:skolem x^) (τ:skolem y^)]
     #:when (free-identifier=? x^ y^)
     '()]
    [[(? τ-mono? t) (τ:var^ x^)]
     (modify-type-context #{snoc % (ctx:solution x^ t)})
     '()]
    [[(? τ:con? a) (? τ:con? b)]
     #:when (τ=? a b)
     '()]
    [[(τ:app a b) (τ:app c d)]
     (let ([x (unify-instance-head a c)])
       (and x (let ([y (unify-instance-head b d)])
                (and y (append x y)))))]
    [[a (τ:∀ x b)]
     (let ([x^ (generate-temporary x)])
       (modify-type-context #{snoc % (ctx:var^ x^)})
       (unify-instance-head a (inst b x (τ:var^ x^))))]
    [[a (τ:qual constr b)]
     (and~>> (unify-instance-head a b)
             (cons constr))]
    [[_ _]
     #f]))

(define/contract (lookup-instance! constr #:src src)
  (-> constr? #:src syntax? (values class:instance? (listof constr?)))
  (match-define (τ:app (τ:con class-id _) (app apply-current-subst t)) constr)
  (define class (syntax-local-value class-id)) ; FIXME: handle when this isn’t a class:info
  (apply values
         (or (for/or ([instance (in-list (current-instances-of-class class))])
               (let ([old-type-context (current-type-context)])
                 (let ([constrs (unify-instance-head t (class:instance-t instance))])
                   (if constrs (list instance constrs)
                       (begin (current-type-context old-type-context) #f)))))
             (raise-syntax-error 'typechecker
                                 (~a "could not deduce " (τ->string (apply-current-subst constr)))
                                 src))))

;; ---------------------------------------------------------------------------------------------------

(define type-transforming?-param (make-parameter #f))
(define (type-transforming?) (type-transforming?-param))

(define-syntax-class type
  #:attributes [τ expansion]
  #:opaque
  [pattern t:expr
           #:with expansion (local-expand-type #'t)
           #:attr τ (syntax-property (attribute expansion) 'τ)
           #:when (τ? (attribute τ))])

(define (parse-type stx)
  (syntax-parse stx
    #:context 'parse-type
    [t:type (attribute t.τ)]))

(define/contract (local-expand-type stx)
  (-> syntax? syntax?)
  (parameterize ([type-transforming?-param #t])
    (local-expand stx 'expression '())))

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
