#lang curly-fn racket/base

(require (for-template racket/base)
         racket/contract
         racket/function
         racket/list
         racket/match
         racket/syntax
         syntax/parse
         threading

         higher-rank/private/util/list
         higher-rank/private/util/stx)

(provide (contract-out [struct τ:var ([x identifier?])]
                       [struct τ:var^ ([x^ identifier?])]
                       [struct τ:-> ([a τ?] [b τ?])]
                       [struct τ:∀ ([x identifier?] [t τ?])]
                       [struct ctx:var ([x identifier?])]
                       [struct ctx:var^ ([x^ identifier?])]
                       [struct ctx:assump ([x identifier?] [t τ?])]
                       [struct ctx:solution ([x^ identifier?] [t τ?])]
                       [struct ctx:marker ([x^ identifier?])])
         τ:unit τ:unit? τ=? τ-mono? τ-vars^ τ->string τ-wf! current-τ-wf! inst
         τ<:! τ-inst-l! τ-inst-r! τ⇐/λ! τ⇐! τ⇒! τ⇒app!
         ctx-elem? ctx? ctx-elem=? ctx-member? ctx-until ctx-split current-ctx-split
         ctx-find-solution current-ctx-solution apply-subst apply-current-subst
         current-type-context modify-type-context
         type τ-stx-token attach-type attach-expected
         get-type get-expected local-expand/get-type make-typed-var-transformer)

(define τ:unit '#s(TUnit))
(struct τ:var (x) #:prefab)
(struct τ:var^ (x^) #:prefab)
(struct τ:-> (a b) #:prefab)
(struct τ:∀ (x t) #:prefab)

(define (τ:unit? x) (equal? τ:unit x))
(define (τ? x) ((disjoin τ:unit? τ:var? τ:var^? τ:->? τ:∀?) x))
(define/contract τ=?
  (-> τ? τ? boolean?)
  (match-lambda**
   [[(== τ:unit) (== τ:unit)] #t]
   [[(τ:var x) (τ:var y)] (free-identifier=? x y)]
   [[(τ:var^ x^) (τ:var^ y^)] (free-identifier=? x^ y^)]
   [[(τ:-> a b) (τ:-> c d)] (and (τ=? a c) (τ=? b d))]
   [[(τ:∀ x a) (τ:∀ y b)] (and (free-identifier=? x y) (τ=? a b))]
   [[_ _] #f]))

(define/contract τ-mono?
  (-> τ? boolean?)
  (match-lambda
    [(== τ:unit) #t]
    [(τ:var _) #t]
    [(τ:var^ _) #t]
    [(τ:-> a b) (and (τ-mono? a) (τ-mono? b))]
    [(τ:∀ _ _) #f]))

(define/contract τ-vars^
  (-> τ? (listof identifier?))
  (match-lambda
    [(== τ:unit) '()]
    [(τ:var _) '()]
    [(τ:var^ x^) (list x^)]
    [(τ:-> a b) (append (τ-vars^ a) (τ-vars^ b))]
    [(τ:∀ _ t) (τ-vars^ t)]))

(define/contract (τ->string t)
  (-> τ? string?)
  (format "~a"
          (let ->datum ([t t])
            (match t
              [(== τ:unit) 'Unit]
              [(τ:var x) (syntax-e x)]
              [(τ:var^ x^) (string->symbol (format "~a^" (syntax-e x^)))]
              [(τ:-> a b) `(-> ,(->datum a) ,(->datum b))]
              [(τ:∀ x t) `(∀ ,(syntax-e x) ,(->datum t))]))))

(struct ctx:var (x) #:prefab)
(struct ctx:var^ (x^) #:prefab)
(struct ctx:assump (x t) #:prefab)
(struct ctx:solution (x^ t) #:prefab)
(struct ctx:marker (x^) #:prefab)

(define (ctx-elem? x) ((disjoin ctx:var? ctx:var^? ctx:assump? ctx:solution? ctx:marker?) x))
(define (ctx? x) ((listof ctx-elem?) x))
(define/contract ctx-elem=?
  (-> ctx-elem? ctx-elem? boolean?)
  (match-lambda**
   [[(ctx:var x) (ctx:var y)] (free-identifier=? x y)]
   [[(ctx:var^ x) (ctx:var^ y)] (free-identifier=? x y)]
   [[(ctx:assump x a) (ctx:assump y b)] (and (free-identifier=? x y) (τ=? a b))]
   [[(ctx:solution x^ a) (ctx:solution y^ b)] (and (free-identifier=? x^ y^) (τ=? a b))]
   [[(ctx:marker x^) (ctx:marker y^)] (free-identifier=? x^ y^)]
   [[_ _] #f]))
(define/contract (ctx-member? ctx elem)
  (-> ctx? ctx-elem? boolean?)
  (and (member elem ctx ctx-elem=?) #t))
(define/contract (ctx-until ctx elem)
  (-> ctx? ctx-elem? ctx?)
  (until ctx elem ctx-elem=?))

(define/contract ctx-split
  (-> ctx? ctx-elem? ctx-elem? ... (listof ctx?))
  (case-lambda
    [(ctx elem)
     (let ([idx (index-of ctx elem ctx-elem=?)])
       (and idx (let-values ([(a b) (split-at ctx idx)])
                  (list a (drop b 1)))))]
    [(ctx elem . elems)
     (let ([ctx* (ctx-split ctx elem)])
       (and ctx* (cons (first ctx*) (apply ctx-split (second ctx*) elems))))]))
(define/contract (current-ctx-split elem . elems)
  (-> ctx-elem? ctx-elem? ... (listof ctx?))
  (apply ctx-split (current-type-context) elem elems))

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
    [(== τ:unit) (void)]
    [(τ:var x) (if (ctx-member? ctx (ctx:var x)) (void)
                   (raise-syntax-error #f "unbound type variable" x))]
    [(τ:var^ x^) (if (or (ctx-member? ctx (ctx:var^ x^))
                         (ctx-find-solution ctx x^))
                     (void)
                     (raise-syntax-error #f "unbound existential variable" x^))]
    [(τ:-> a b) (τ-wf! ctx a) (τ-wf! ctx b)]
    [(τ:∀ x t) (τ-wf! (snoc ctx (ctx:var x)) t)]))
(define/contract (current-τ-wf! t)
  (-> τ? void?)
  (τ-wf! (current-type-context) t))

(define/contract (apply-subst ctx t)
  (-> ctx? τ? τ?)
  (match t
    [(== τ:unit) τ:unit]
    [(τ:var _) t]
    [(τ:var^ x^) (let ([s (ctx-find-solution ctx x^)])
                   (if s (apply-subst ctx s) t))]
    [(τ:-> a b) (τ:-> (apply-subst ctx a) (apply-subst ctx b))]
    [(τ:∀ x t) (τ:∀ x (apply-subst ctx t))]))
(define (apply-current-subst t)
  (apply-subst (current-type-context) t))

(define/contract (inst t x s)
  (-> τ? identifier? τ? τ?)
  (match t
    [(== τ:unit) τ:unit]
    [(τ:var y) (if (free-identifier=? x y) s t)]
    [(τ:var^ _) t]
    [(τ:-> a b) (τ:-> (inst a x s) (inst b x s))]
    [(τ:∀ x t*) (τ:∀ (inst t* x s))]))

(define/contract current-type-context (parameter/c ctx?) (make-parameter '()))
(define/contract (modify-type-context f)
  (-> (-> ctx? ctx?) void?)
  (current-type-context (f (current-type-context))))

(define/contract τ<:!
  (-> τ? τ? void?)
  (match-lambda**
   ; <:Unit
   [[(== τ:unit) (== τ:unit)]
    (void)]
   ; <:Var
   [[(τ:var x) (τ:var y)]
    #:when (free-identifier=? x y)
    (void)]
   ; <:Exvar
   [[(τ:var^ x^) (τ:var^ y^)]
    #:when (free-identifier=? x^ y^)
    (void)]
   ; <:→
   [[(τ:-> a b) (τ:-> c d)]
    (τ<:! c a)
    (τ<:! b d)]
   ; <:∀L
   [[(τ:∀ x a) b]
    (let* ([x^ (generate-temporary x)]
           [a* (inst a x (τ:var^ x^))])
      (modify-type-context #{append % (list (ctx:marker x^) (ctx:var^ x^))})
      (τ<:! a* b)
      (modify-type-context #{ctx-until % (ctx:marker x^)}))]
   ; <:∀R
   [[a (τ:∀ x b)]
    (modify-type-context #{snoc % (ctx:var x)})
    (τ<:! a b)
    (modify-type-context #{ctx-until % (ctx:var x)})]
   ; <:InstantiateL
   [[(τ:var^ x^) a]
    #:when (not (member x^ (τ-vars^ a) free-identifier=?))
    (τ-inst-l! x^ a)]
   ; <:InstantiateR
   [[a (τ:var^ x^)]
    #:when (not (member x^ (τ-vars^ a) free-identifier=?))
    (τ-inst-r! a x^)]
   [[a b]
    (error (format "type mismatch: expected ~a, given ~a" (τ->string b) (τ->string a)))]))

(define/contract (τ-inst-l! x^ t)
  (-> identifier? τ? void?)
  (match t
    ; InstLSolve
    [(? τ-mono?) {=> fail}
                 (match-let ([(list l r) (or (current-ctx-split (ctx:var^ x^)) (fail))])
                   (with-handlers ([exn:fail:syntax? (λ (exn) (fail))])
                     (τ-wf! l t))
                   (current-type-context (append l (list (ctx:solution x^ t)) r)))]
    ; InstLReach
    [(τ:var^ y^) {=> fail}
                 (match-let ([(list l m r) (or (current-ctx-split (ctx:var^ x^) (ctx:var^ y^)) (fail))])
                   (current-type-context (append l (list (ctx:var^ x^)) m (list (ctx:solution y^ (τ:var^ x^))) r)))]
    ; InstLArr
    [(τ:-> a b) {=> fail}
                (match-let ([(list l r) (or (current-ctx-split (ctx:var^ x^)) (fail))]
                            [x1^ (generate-temporary x^)]
                            [x2^ (generate-temporary x^)])
                  (current-type-context (append l (list (ctx:var^ x2^) (ctx:var^ x1^) (ctx:solution x^ (τ:-> (τ:var^ x1^) (τ:var^ x2^)))) r))
                  (τ-inst-r! a x1^)
                  (τ-inst-l! x2^ (apply-current-subst b)))]
    ; InstLAllR
    [(τ:∀ x t*)
     (modify-type-context #{snoc % (ctx:var x)})
     (τ-inst-l! x^ t*)
     (match-let ([(list ctx _) (current-ctx-split (ctx:var x))])
       (current-type-context ctx))]
    [_ (error 'τ-inst-l! (format "failed to instantiate ~a to a subtype of ~a"
                                 (τ->string (τ:var^ x^)) (τ->string t)))]))

(define/contract (τ-inst-r! t x^)
  (-> τ? identifier? void?)
  (match t
    ; InstRSolve
    [(? τ-mono?) {=> fail}
                 (match-let ([(list l r) (or (current-ctx-split (ctx:var^ x^)) (fail))])
                   (with-handlers ([exn:fail:syntax? (λ (exn) (fail))])
                     (τ-wf! l t))
                   (current-type-context (append l (list (ctx:solution x^ t)) r)))]
    ; InstRReach
    [(τ:var^ y^) {=> fail}
                 (match-let ([(list l m r) (or (current-ctx-split (ctx:var^ x^) (ctx:var^ y^)) (fail))])
                   (current-type-context (append l (list (ctx:var^ x^)) m (list (ctx:solution y^ (τ:var^ x^))) r)))]
    ; InstRArr
    [(τ:-> a b) {=> fail}
                (match-let ([(list l r) (or (current-ctx-split (ctx:var^ x^)) (fail))]
                            [x1^ (generate-temporary x^)]
                            [x2^ (generate-temporary x^)])
                  (current-type-context (append l (list (ctx:var^ x2^) (ctx:var^ x1^) (ctx:solution x^ (τ:-> (τ:var^ x1^) (τ:var^ x2^)))) r))
                  (τ-inst-l! x1^ a)
                  (τ-inst-r! (apply-current-subst b) x2^))]
    ; InstRAllL
    [(τ:∀ x t*)
     (let ([y^ (generate-temporary x)])
       (modify-type-context #{append % (list (ctx:marker y^) (ctx:var^ y^))})
       (τ-inst-r! (inst t* x (τ:var^ y^)) x^)
       (match-let ([(list ctx _) (current-ctx-split (ctx:marker y^))])
         (current-type-context ctx)))]
    [_ (error 'τ-inst-r! (format "failed to instantiate ~a to a supertype of ~a"
                                 (τ->string (τ:var^ x^)) (τ->string t)))]))

;; -------------------------------------------------------------------------------------------------

(define/contract (τ⇐/λ! e t bindings)
  (-> syntax? τ? (listof (cons/c identifier? τ?)) (values (listof identifier?) syntax?))
  (current-τ-wf! t)
  (match t
    [(τ:∀ x a)
     (modify-type-context #{snoc % (ctx:var x)})
     (begin0
       (τ⇐/λ! e a bindings)
       (modify-type-context #{ctx-until % (ctx:var x)}))]
    [_
     (define/syntax-parse [x ...] (map car bindings))
     (define/syntax-parse [x- ...] (generate-temporaries (attribute x)))
     (define/syntax-parse [t_x ...] (map (λ~> cdr preservable-property->expression) bindings))
     (define-values [xs- e-]
       (syntax-parse (local-expand #`(λ (x- ...)
                                       (let-syntax ([x (make-typed-var-transformer #'x- t_x)] ...)
                                         #,(attach-expected e t)))
                                   'expression '())
         #:literals [#%plain-lambda let-values]
         [(#%plain-lambda (x-* ...) (let-values _ (let-values _ e-)))
          (values (attribute x-*) #'e-)]))
     (define t_e (get-type e-))
     (unless t_e (raise-syntax-error #f "no inferred type" e))
     (τ<:! (apply-current-subst t_e) (apply-current-subst t))
     (values xs- e-)]))

(define/contract (τ⇐! e t)
  (-> syntax? τ? syntax?)
  (match-let-values ([(_ e-) (τ⇐/λ! e t '())])
    e-))

(define/contract (τ⇒! e)
  (-> syntax? (values syntax? τ?))
  (define-values [e- τ_e] (local-expand/get-type e))
  (unless τ_e (raise-syntax-error #f "no inferred type" e))
  (values e- τ_e))

(define/contract (τ⇒app! t e)
  (-> τ? syntax? (values syntax? τ?))
  (match t
    [(τ:var^ x^)
     (match-let ([(list l r) (current-ctx-split (ctx:var^ x^))]
                 [x1^ (generate-temporary x^)]
                 [x2^ (generate-temporary x^)])
       (current-type-context (append l (list (ctx:var^ x2^) (ctx:var^ x1^) (ctx:solution x^ (τ:-> (τ:var x1^) (τ:var x2^)))) r))
       (values (τ⇐! e (τ:var^ x1^)) (τ:var^ x2^)))]
    [(τ:-> a b)
     (values (τ⇐! e a) b)]
    [(τ:∀ x t)
     (let ([x^ (generate-temporary x)])
       (modify-type-context #{snoc % (ctx:var^ x^)})
       (τ⇒app! (inst t x (τ:var^ x^)) e))]
    [_ (raise-syntax-error #f (format "cannot apply expression of type ~a to expression ~a"
                                      (τ->string t) (syntax->datum e))
                           e)]))

;; -------------------------------------------------------------------------------------------------

(define-syntax-class type
  #:attributes [τ]
  #:opaque
  [pattern t:expr
           #:with t- (local-expand #'t 'expression '())
           #:attr τ (syntax-property #'t- 'τ)
           #:when (τ? (attribute τ))])

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
