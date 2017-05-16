#lang curly-fn racket/base

(require (for-template racket/base)
         (for-syntax racket/base
                     syntax/parse
                     syntax/transformer)
         racket/contract
         racket/format
         racket/function
         racket/list
         racket/match
         racket/syntax
         syntax/parse
         threading

         hackett/private/util/list
         hackett/private/util/stx)

(provide (contract-out [struct τ:var ([x identifier?])]
                       [struct τ:var^ ([x^ identifier?])]
                       [struct τ:con ([name identifier?] [constructors (or/c (listof syntax?) #f)])]
                       [struct τ:app ([a τ?] [b τ?])]
                       [struct τ:∀ ([x identifier?] [t τ?])]
                       [struct ctx:var ([x identifier?])]
                       [struct ctx:var^ ([x^ identifier?])]
                       [struct ctx:skolem ([x^ identifier?])]
                       [struct ctx:assump ([x identifier?] [t τ?])]
                       [struct ctx:solution ([x^ identifier?] [t τ?])])
         τ? τ:unit τ:-> τ:->? τ:->* τ=? τ-mono? τ-vars^ τ->string τ-wf! current-τ-wf! generalize inst
         τ<:! τ-inst-l! τ-inst-r! τ⇐/λ! τ⇐! τ⇒/λ! τ⇒! τ⇒app! τs⇒!
         ctx-elem? ctx? ctx-elem=? ctx-member? ctx-remove
         ctx-find-solution current-ctx-solution apply-subst apply-current-subst
         current-type-context modify-type-context
         type type-transforming? parse-type τ-stx-token make-type-variable-transformer
         attach-type attach-expected get-type get-expected local-expand/get-type
         make-typed-var-transformer)

(struct τ:var (x) #:prefab)
(struct τ:var^ (x^) #:prefab)
(struct τ:skolem (x^) #:prefab)
(struct τ:con (name constructors) #:prefab)
(struct τ:app (a b) #:prefab)
(struct τ:∀ (x t) #:prefab)

(define τ:unit (τ:con #'Unit #f))
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

(define (τ? x) ((disjoin τ:var? τ:var^? τ:skolem? τ:con? τ:app? τ:∀?) x))
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

(define/contract τ-mono?
  (-> τ? boolean?)
  (match-lambda
    [(τ:var _) #t]
    [(τ:var^ _) #t]
    [(τ:skolem _) #t]
    [(τ:con _ _) #t]
    [(τ:app a b) (and (τ-mono? a) (τ-mono? b))]
    [(τ:∀ _ _) #f]))

(define/contract τ-vars^
  (-> τ? (listof identifier?))
  (match-lambda
    [(τ:var _) '()]
    [(τ:var^ x^) (list x^)]
    [(τ:skolem _) '()]
    [(τ:con _ _) '()]
    [(τ:app a b) (remove-duplicates (append (τ-vars^ a) (τ-vars^ b)) free-identifier=?)]
    [(τ:∀ _ t) (τ-vars^ t)]))

(define/contract (τ->string t)
  (-> τ? string?)
  (format "~a"
          (let ->datum ([t t])
            (match t
              [(== τ:unit) 'Unit]
              [(τ:var x) (syntax-e x)]
              [(τ:var^ x^) (string->symbol (format "~a^" (syntax-e x^)))]
              [(τ:skolem x^) (syntax-e x^)]
              [(τ:con name _) (syntax-e name)]
              [(? τ:app?)
               (let flatten-app ([t t])
                 (match t
                   [(τ:app a b) (append (flatten-app a) (list (->datum b)))]
                   [other (list (->datum other))]))]
              [(τ:∀ x t)
               (let flatten-forall ([xs (list x)]
                                    [t t])
                 (match t
                   [(τ:∀ x t) (flatten-forall (cons x xs) t)]
                   [other `(∀ ,(map syntax-e (reverse xs)) ,(->datum t))]))]))))

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
    [(τ:∀ x t) (τ-wf! (snoc ctx (ctx:var x)) t)]))
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
    [(τ:∀ x t) (τ:∀ x (apply-subst ctx t))]))
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
    [(== τ:unit) τ:unit]
    [(τ:var y) (if (free-identifier=? x y) s t)]
    [(τ:var^ _) t]
    [(τ:skolem _) t]
    [(τ:con _ _) t]
    [(τ:app a b) (τ:app (inst a x s) (inst b x s))]
    [(τ:∀ v t*) (τ:∀ v (inst t* x s))]))

(define/contract current-type-context (parameter/c ctx?) (make-parameter '()))
(define/contract (modify-type-context f)
  (-> (-> ctx? ctx?) void?)
  (current-type-context (f (current-type-context))))

(define/contract (τ<:! a b #:src src)
  (-> τ? τ? #:src syntax? void?)
  (match* [(apply-current-subst a) (apply-current-subst b)]
   ; <:Con
   [[(? τ:con? a) (? τ:con? b)]
    #:when (τ=? a b)
    (void)]
   ; <:Var
   [[(τ:var x) (τ:var y)]
    #:when (free-identifier=? x y)
    (void)]
   ; <:Exvar
   [[(τ:var^ x^) (τ:var^ y^)]
    #:when (free-identifier=? x^ y^)
    (void)]
   [[(τ:skolem x^) (τ:skolem y^)]
    #:when (free-identifier=? x^ y^)
    (void)]
   ; <:→
   ; we need to handle → specially since it is allowed to be applied to polytypes
   [[(τ:->* a b) (τ:->* c d)]
    (τ<:! c a #:src src)
    (τ<:! b d #:src src)]
   ; <:App
   [[(τ:app a b) (τ:app c d)]
    (for ([t (in-list (list a b c d))])
      (unless (τ-mono? t)
        (raise-syntax-error #f (~a "illegal polymorphic type " (τ->string t)
                                   ", impredicative polymorphism is not supported") src)))
    (τ<:! a c #:src src)
    (τ<:! b d #:src src)]
   ; <:∀L
   [[(τ:∀ x a) b]
    (let* ([x^ (generate-temporary x)]
           [a* (inst a x (τ:var^ x^))])
      (modify-type-context #{snoc % (ctx:var^ x^)})
      (τ<:! a* b #:src src))]
   ; <:∀R
   [[a (τ:∀ x b)]
    (let* ([x^ (generate-temporary x)]
           [b* (inst b x (τ:skolem x^))])
      (modify-type-context #{snoc % (ctx:skolem x^)})
      (τ<:! a b #:src src)
      (modify-type-context #{ctx-remove % (ctx:skolem x^)}))]
   ; <:InstantiateL
   [[(τ:var^ x^) a]
    #:when (not (member x^ (τ-vars^ a) free-identifier=?))
    (τ-inst-l! x^ a)]
   ; <:InstantiateR
   [[a (τ:var^ x^)]
    #:when (not (member x^ (τ-vars^ a) free-identifier=?))
    (τ-inst-r! a x^)]
   [[a b]
    (raise-syntax-error 'typechecker
                        (~a "type mismatch\n"
                            "  between: " (τ->string b) "\n"
                            "      and: " (τ->string a))
                        src)]))

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

;; -------------------------------------------------------------------------------------------------

(define/contract (τ⇒/λ! e bindings)
  (-> syntax? (listof (cons/c identifier? τ?)) (values (listof identifier?) syntax? τ?))
  (define/syntax-parse [x ...] (map car bindings))
  (define/syntax-parse [x- ...] (generate-temporaries (attribute x)))
  (define/syntax-parse [t_x ...] (map (λ~> cdr preservable-property->expression) bindings))
  (define-values [xs- e-]
    (syntax-parse (local-expand #`(λ (x- ...)
                                    (let-syntax ([x (make-typed-var-transformer #'x- t_x)] ...)
                                      #,e))
                                'expression '())
      #:literals [#%plain-lambda let-values]
      [(#%plain-lambda (x-* ...) (let-values _ (let-values _ e-)))
       (values (attribute x-*) #'e-)]))
  (define t_e (get-type e-))
  (unless t_e (raise-syntax-error #f "no inferred type" e))
  (values xs- e- t_e))

(define/contract (τ⇐/λ! e t bindings)
  (-> syntax? τ? (listof (cons/c identifier? τ?)) (values (listof identifier?) syntax?))
  (current-τ-wf! t)
  (match t
    [(τ:∀ x a)
     (modify-type-context #{snoc % (ctx:var x)})
     (begin0
       (τ⇐/λ! e a bindings)
       (modify-type-context #{ctx-remove % (ctx:var x)}))]
    [_
     (define-values [xs- e- t_e] (τ⇒/λ! (attach-expected e t) bindings))
     (τ<:! t_e t #:src e)
     (values xs- e-)]))

(define/contract (τ⇒! e)
  (-> syntax? (values syntax? τ?))
  (match-let-values ([(_ e- t_e) (τ⇒/λ! e '())])
    (values e- t_e)))

(define/contract (τ⇐! e t)
  (-> syntax? τ? syntax?)
  (match-let-values ([(_ e-) (τ⇐/λ! e t '())])
    e-))

(define/contract (τ⇒app! t e)
  (-> τ? syntax? (values syntax? τ?))
  (match t
    [(τ:var^ x^)
     (let ([x1^ (generate-temporary x^)]
           [x2^ (generate-temporary x^)])
       (modify-type-context #{append % (list (ctx:var^ x2^) (ctx:var^ x1^) (ctx:solution x^ (τ:->* (τ:var x1^) (τ:var x2^))))})
       (values (τ⇐! e (τ:var^ x1^)) (τ:var^ x2^)))]
    [(τ:->* a b)
     (values (τ⇐! e a) b)]
    [(τ:∀ x t)
     (let ([x^ (generate-temporary x)])
       (modify-type-context #{snoc % (ctx:var^ x^)})
       (τ⇒app! (inst t x (τ:var^ x^)) e))]
    [_ (raise-syntax-error #f (format "cannot apply expression of type ~a to expression ~a"
                                      (τ->string t) (syntax->datum e))
                           e)]))

(define/contract (τs⇒! es)
  (-> (listof syntax?) (values (listof syntax?) (listof τ?)))
  (for/fold ([es- '()]
             [ts '()])
            ([e (in-list es)])
    (let-values ([(e- t) (τ⇒! e)])
      (values (snoc es- e-) (snoc ts t)))))

;; -------------------------------------------------------------------------------------------------

(define type-transforming?-param (make-parameter #f))
(define (type-transforming?) (type-transforming?-param))

(define-syntax-class type
  #:attributes [τ]
  #:opaque
  [pattern t:expr
           #:with t- (parameterize ([type-transforming?-param #t])
                       (local-expand #'t 'expression '()))
           #:attr τ (syntax-property #'t- 'τ)
           #:when (τ? (attribute τ))])

(define (parse-type stx)
  (syntax-parse stx
    #:context 'parse-type
    [t:type (attribute t.τ)]))

(define/contract (make-type-variable-transformer t)
  (-> τ? any)
  (make-variable-like-transformer (τ-stx-token t)))

;; -------------------------------------------------------------------------------------------------

(define/contract (τ-stx-token t)
  (-> τ? syntax?)
  (syntax-property #'(void) 'τ t #t))
(define/contract (attach-type stx t)
  (-> syntax? τ? syntax?)
  (syntax-property stx ': t #t))
(define/contract (attach-expected stx t)
  (-> syntax? τ? syntax?)
  (syntax-property stx ':⇐ t #t))

(define/contract (get-type stx)
  (-> syntax? (or/c τ? #f))
  (let loop ([val (syntax-property stx ':)])
    (if (pair? val) (loop (car val)) val)))
(define/contract (get-expected stx)
  (-> syntax? (or/c τ? #f))
  (let loop ([val (syntax-property stx ':⇐)])
    (if (pair? val) (loop (car val)) val)))

(define/contract (local-expand/get-type stx)
  (-> syntax? (values syntax? (or/c τ? #f)))
  (let ([stx* (local-expand stx 'expression '())])
    (values stx* (get-type stx*))))

(define/contract (make-typed-var-transformer x t)
  (-> identifier? τ? any)
  (make-variable-like-transformer (attach-type x t)))
