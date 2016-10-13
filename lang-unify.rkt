#lang curly-fn racket/base

(provide λ +
         (rename-out [hash-percent-app #%app]
                     [hash-percent-datum #%datum]
                     [hash-percent-module-begin #%module-begin]))

(require (for-syntax racket/hash
                     syntax/id-table)
         (except-in macrotypes/typecheck #%module-begin)
         (postfix-in - racket/base)
         (prefix-in kernel: '#%kernel)
         macro-debugger/syntax-browser)

;; ---------------------------------------------------------------------------------------------------

(define-type-constructor →
  #:arity = 2
  #:arg-variances (const (list covariant contravariant)))

(define-type-constructor ∀ #:bvs >= 0)

(define-type-constructor τ~ #:arity = 2)

(define-base-type Integer)
(define-base-type String)

(begin-for-syntax
  (define (propagate-originalness new-stx old-stx)
    (if (or (syntax-original? old-stx)
            (syntax-property old-stx 'original-for-check-syntax))
        (syntax-property new-stx 'original-for-check-syntax #t)
        new-stx))
  
  (define (fresh)
    (mk-type #`#s(var #,(generate-temporary))))

  (define type->string
    (syntax-parser
      #:context 'type->string
      #:literals [quote]
      ['#s(var ~! α:id)
       (symbol->string (syntax-e #'α))]
      [(~→ τa τb)
       (format "(→ ~a ~a)" (type->string #'τa) (type->string #'τb))]
      [(~∀ [τv ...] τ)
       (format "(∀ ~a ~a)" (map type->string (attribute τv)) (type->string #'τ))]
      [(~τ~ τa τb)
       (format "(τ~~ ~a ~a)" (type->string #'τa) (type->string #'τb))]
      [~Integer "Integer"]
      [~String "String"]
      #;[_ (type->str this-syntax)]))

  (let ([old-type=? (current-type=?)])
    (current-type=?
     (λ (τa τb)
       (syntax-parse (list τa τb)
         [(#s(var a:id) #s(var b:id))
          (free-identifier=? #'a #'b)]
         [(#s(var _) _) #f]
         [(_ #s(var _)) #f]
         [(_ _) (old-type=? τa τb)]))))

  (define (infer+erase stx #:ctx [ctx #'()])
    (define wrapped-stx
      (syntax-parse ctx
        [([x:id : τ] ...)
         #:with (x- ...) (for/list ([x-stx (in-list (attribute x))])
                           (let ([tmp (generate-temporary x-stx)])
                             (datum->syntax tmp (syntax-e tmp) x-stx)))
         #`(λ- (x- ...)
               (let-syntax ([x (make-variable-like-transformer (⊢ x- : τ))]
                            ...)
                 #,stx))]))
    (define-values [τ xs- stx-]
      (syntax-parse (local-expand wrapped-stx 'expression null)
        #:literals [kernel:lambda kernel:let-values]
        [(kernel:lambda xs-
           (kernel:let-values _
             (kernel:let-values _ body)))
         (values (typeof #'body) #'xs- #'body)]))
    (list τ xs- stx-))

  (define (assign-constraint stx c)
    (syntax-property stx
                     'constraints
                     (list (syntax-property (syntax-local-introduce ((current-type-eval) c))
                                            'constraint-source stx #t))
                     #t)))

(define-syntax-parser λ
  [(_ x:id e:expr)
   #:with τv (fresh)
   #:with [τ [x-] e-] (infer+erase #'e #:ctx #'([x : τv]))
   (⊢ (λ- (x-) e-) : (→ τv τ))])

(define-syntax-parser hash-percent-app
  [(_ fn arg)
   #:with τv (fresh)
   #:with [τ_fn [] fn-] (infer+erase #'fn)
   #:with [τ_arg [] arg-] (infer+erase #'arg)
   (assign-constraint (⊢ #,(syntax/loc this-syntax
                             (#%app- fn- arg-)) : τv)
                      #'{τ_fn . τ~ . (→ τ_arg τv)})])

(define-syntax-parser hash-percent-datum
  [(_ . n:integer)
   (⊢ (#%datum- . n) : Integer)]
  [(_ . n:str)
   (⊢ (#%datum- . n) : String)]
  [(_ . x)
   (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)])

(define ((+/c a) b) (+- a b))
(define-syntax + (make-variable-like-transformer
                  (⊢ +/c : (→ Integer (→ Integer Integer)))))

(begin-for-syntax
  (define/match (flatten-syntax-property-value val)
    [(#f)
     '()]
    [((cons a b))
     (append (flatten-syntax-property-value a)
             (flatten-syntax-property-value b))]
    [((? list?))
     (append-map flatten-syntax-property-value val)]
    [(_)
     (list val)])

  (define (collect-properties stx key)
    (define (get-properties stx)
      (flatten-syntax-property-value (syntax-property stx key)))
    (let recur ([stx stx])
      (syntax-parse stx
        [(elem ...+ . cdr)
         (append (get-properties this-syntax)
                 (append-map recur (attribute elem))
                 (recur #'cdr))]
        [_ (get-properties this-syntax)])))

  (define (collect-constraints stx)
    (collect-properties stx 'constraints)))

(define-syntax-parser hash-percent-module-begin
  [(_ . body)
   #:with expanded (local-expand #'(#%plain-module-begin- . body)
                                 'module-begin null)
   #:do [(define subst (solve-constraints (collect-constraints #'expanded)))]
   (apply-substitutions-to-types subst #'expanded)])

(begin-for-syntax
  ; left-biased union of immutable free-id tables
  (define (free-id-table-union a b)
    (let ([t (make-free-id-table)])
      (for ([(k v) (in-free-id-table b)])
        (free-id-table-set! t k v))
      (for ([(k v) (in-free-id-table a)])
        (free-id-table-set! t k v))
      (make-immutable-free-id-table t)))
  
  (define (compose-substs a b)
    (free-id-table-union
     (make-immutable-free-id-table
      (for/list ([(k v) (in-free-id-table b)])
        (cons k (apply-subst a v))))
     a))

  (define (apply-subst subst stx)
    (syntax-parse stx
      #:context 'apply-subst
      #:literals [quote]
      ['#s(var τv:id)
       (free-id-table-ref subst #'τv stx)]
      [(~→ τa τb)
       ((current-type-eval)
        #`(→ #,(apply-subst subst #'τa)
             #,(apply-subst subst #'τb)))]
      [(~∀ τvs τ)
       ((current-type-eval)
        #`(∀ τvs #,(apply-subst subst #'τ)))]
      [(~τ~ τa τb)
       (datum->syntax this-syntax
                      (syntax-e ((current-type-eval)
                                 #`(τ~ #,(apply-subst subst #'τa)
                                       #,(apply-subst subst #'τb))))
                      this-syntax this-syntax)]
      [_ stx]))

  (define (bind-subst τv τ)
    (make-immutable-free-id-table
     (list (cons τv τ))))

  (define (unify τa τb #:src src)
    (if ((current-type=?) τa τb)
        (make-immutable-free-id-table)
        (syntax-parse (list τa τb)
          #:literals [quote]
          [('#s(var τv:id) τ)
           (bind-subst #'τv #'τ)]
          [(τ '#s(var τv:id))
           (bind-subst #'τv #'τ)]
          [((~→ τa τb) (~→ τc τd))
           (compose-substs (unify #'τa #'τc #:src src)
                           (unify #'τb #'τd #:src src))]
          [(_ _)
           (raise-syntax-error #f (format "could not unify ~a with ~a"
                                          (type->string τa) (type->string τb))
                               src)])))

  (define (solve-constraints cs)
    (let recur ([cs cs]
                [subst (make-immutable-free-id-table)])
      (if (empty? cs) subst
          (syntax-parse (first cs)
            #:context 'solve-constraints
            [(~τ~ τa τb)
             (let ([subst* (unify #'τa #'τb
                                  #:src (syntax-property this-syntax 'constraint-source))])
               (recur (map #{apply-subst subst* %} (rest cs))
                      (compose-substs subst* subst)))]))))

  (define (apply-substitutions-to-syntax subst stx)
    (let recur ([stx stx])
      (syntax-rearm
       (syntax-parse (syntax-disarm stx (current-code-inspector))
         #:literals [quote]
         ['#s(var α:id)
          (free-id-table-ref subst #'α this-syntax)]
         [(elem . rest)
          (datum->syntax this-syntax (cons (recur #'elem) (recur #'rest))
                         this-syntax this-syntax)]
         [_ this-syntax])
       stx)))

  (define (apply-substitutions-to-props subst stx prop)
    (define (perform-substitution stx)
      (if (syntax-property stx prop)
          (syntax-property stx prop (apply-substitutions-to-syntax
                                     subst
                                     (syntax-property stx prop))
                           (syntax-property-preserved? stx prop))
          stx))
    (let recur ([stx stx])
      (syntax-rearm
       (syntax-parse (syntax-disarm stx (current-code-inspector))
         [(elem . rest)
          (perform-substitution
           (datum->syntax this-syntax (cons (recur #'elem) (recur #'rest))
                          this-syntax this-syntax))]
         [_ (perform-substitution this-syntax)])
       stx)))

  (define (apply-substitutions-to-types subst stx)
    (apply-substitutions-to-props subst stx ':)))

;; ---------------------------------------------------------------------------------------------------
;; definitions

#;(define-typed-syntax def
  #:datum-literals [:]
  [(_ x:id : τ:type e:expr) ≫
   #:with y (generate-temporary #'x)
   ---------------------------------------
   [≻ (begin
        (define- y (ann e : τ.norm))
        (define-syntax x (make-variable-like-transformer (⊢ y : τ.norm))))]]
  [(_ x:id e:expr) ≫
   [⊢ e ≫ e- ⇒ τ]
   #:with y (generate-temporary #'x)
   ---------------
   [≻ (begin-
        (define- y e-)
        (define-syntax x (make-variable-like-transformer (⊢ y : τ))))]])
