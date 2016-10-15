#lang curly-fn racket/base

(provide λ let +
         (rename-out [hash-percent-app #%app]
                     [hash-percent-datum #%datum]
                     [hash-percent-module-begin #%module-begin]))

(require (for-syntax racket/hash
                     syntax/id-table
                     "util/stx.rkt")
         (except-in macrotypes/typecheck #%module-begin)
         (postfix-in - racket/base)
         (prefix-in kernel: '#%kernel)
         macro-debugger/syntax-browser)

;; ---------------------------------------------------------------------------------------------------
;; type constructors

(define-type-constructor →
  #:arity = 2
  #:arg-variances (const (list covariant contravariant)))

(define-type-constructor τ~ #:arity = 2)

(define-base-type Integer)
(define-base-type String)

;; ---------------------------------------------------------------------------------------------------
;; types

(begin-for-syntax
  (define type->string
    (syntax-parser
      #:context 'type->string
      #:literals [quote]
      ['#s(var ~! α:id)
       (symbol->string (syntax-e #'α))]
      [(~→ τa τb)
       (format "(→ ~a ~a)" (type->string #'τa) (type->string #'τb))]
      ['#s(∀ [τv ...] τ)
       (format "(∀ ~a ~a)" (map type->string (attribute τv)) (type->string #'τ))]
      [(~τ~ τa τb)
       (format "(τ~~ ~a ~a)" (type->string #'τa) (type->string #'τb))]
      [~Integer "Integer"]
      [~String "String"]
      [:id (type->str this-syntax)]))

  (let ([old-type=? (current-type=?)])
    (current-type=?
     (λ (τa τb)
       (syntax-parse (list τa τb)
         [(#s(var a:id) #s(var b:id))
          (free-identifier=? #'a #'b)]
         [(#s(var _) _) #f]
         [(_ #s(var _)) #f]
         [(_ _) (old-type=? τa τb)]))))

  (let ([old-type-eval (current-type-eval)])
    (current-type-eval
     (syntax-parser
       #:literals [quote]
       ['#s(∀ τvs τ)
        (old-type-eval #`#s(∀ τvs #,((current-type-eval) #'τ)))]
       [_ (old-type-eval this-syntax)])))

  ; Generates a fresh type variable.
  (define (fresh)
    ((current-type-eval)
     (mk-type #`#s(var #,(generate-temporary)))))

  (define (infer+erase stx #:ctx [ctx #'()])
    (define wrapped-stx
      (syntax-parse ctx
        [([x:id : τ] ...)
         #:with (x- ...) (for/list ([x-stx (in-list (attribute x))])
                           (let ([tmp (generate-temporary x-stx)])
                             (datum->syntax tmp (syntax-e tmp) x-stx)))
         #`(λ- (x- ...)
               (let-syntax ([x (make-variable-like-transformer/thunk
                                (λ () (assign-type #'x- (instantiate-type #'τ))))]
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

  ; Given a type, replaces universally quantified type variables with fresh type variables.
  (define instantiate-type
    (syntax-parser
      #:literals [quote]
      ['#s(∀ [α ...] τ)
       (apply-subst
        (make-immutable-free-id-table
         (for/list ([var (in-list (attribute α))])
           (cons var (fresh))))
        #'τ)]
      [_ this-syntax]))

  ; Given a type, finds all free type variables and universally quantifies them using ∀.
  (define (generalize-type stx)
    (define collect-vars
      (syntax-parser
        #:context 'collect-vars
        #:literals [quote]
        ['#s(var α:id)
         (list #'α)]
        [(left . right)
         (remove-duplicates (append (collect-vars #'left)
                                    (collect-vars #'right))
                            free-identifier=?)]
        [_ '()]))
    (let ([free-vars (collect-vars stx)])
      (if (empty? free-vars) stx
          ((current-type-eval)
           #`#s(∀ #,(collect-vars stx) #,stx))))))

;; ---------------------------------------------------------------------------------------------------
;; constraints & substitution

(begin-for-syntax
  ; Attaches a constraint to a syntax object by associating a type with the 'constraint syntax
  ; property. Calls syntax-local-introduce and (current-type-eval) on the provided constraint.
  (define (assign-constraint stx c)
    (syntax-property stx
                     'constraints
                     (list (syntax-property (syntax-local-introduce ((current-type-eval) c))
                                            'constraint-source stx #t))
                     #t))

  ; Returns a list of all constraints in a syntax object by recursively collecting the values of the
  ; 'constraint syntax property.
  (define (collect-constraints stx)
    (collect-properties stx 'constraints))

  ; The empty substitution set.
  (define empty-subst
    (make-immutable-free-id-table))

  ; Creates a substitution set containing exactly one subsitution between the given type variable and
  ; the given type.
  (define (bind-subst τv τ)
    (make-immutable-free-id-table
     (list (cons τv τ))))

  ; Composes two substitution sets by applying one substitution set to the other and taking their
  ; union.
  (define (compose-substs a b)
    (free-id-table-union
     (make-immutable-free-id-table
      (for/list ([(k v) (in-free-id-table b)])
        (cons k (apply-subst a v))))
     a))

  ; Applies a subsitution set to a type or constraint by recursively replacing all substitutable type
  ; variables with their substitutions.
  (define (apply-subst subst stx)
    ((current-type-eval)
     (let recur ([stx stx])
       (syntax-parse stx
         #:context 'apply-subst
         #:literals [quote]
         ['#s(var τv:id)
          (free-id-table-ref subst #'τv stx)]
         ['#s(∀ τvs τ)
          #`#s(∀ τvs #,((current-type-eval)
                        (recur #'τ)))]
         [(~→ τa τb)
          #`(→ #,(recur #'τa)
               #,(recur #'τb))]
         [(~τ~ τa τb)
          (datum->syntax this-syntax
                         (syntax-e #`(τ~ #,(recur #'τa)
                                         #,(recur #'τb)))
                         this-syntax this-syntax)]
         [_ stx]))))

  ; Attempts to unify the two provided types, reporting errors in terms of the provided source syntax
  ; object.
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
           (unify* (list (cons #'τa #'τc)
                         (cons #'τb #'τd))
                   #:src src)]
          [(_ _)
           (raise-syntax-error #f (format "could not unify ~a with ~a"
                                          (type->string τa) (type->string τb))
                               src)])))

  ; Attempts to unify each pair of types provided, propagating the substitutions performed back into
  ; the set of constraints at each step.
  (define (unify* τ_pairs #:src src)
    (match τ_pairs
      ['() (make-immutable-free-id-table)]
      [(list (cons τa τb)
             (cons τas τbs) ...)
       (let* ([subst (unify τa τb #:src src)]
              [subst* (unify* (map cons (map #{apply-subst subst %} τas)
                                        (map #{apply-subst subst %} τbs))
                              #:src src)])
         (compose-substs subst subst*))]))

  ; Given a set of constraints, attempts to solve them with unification.
  (define (solve-constraints cs)
    (let recur ([cs cs]
                [subst (make-immutable-free-id-table)])
      (if (empty? cs) subst
          (syntax-parse (first cs)
            #:context 'solve-constraints
            [(~τ~ τa τb)
             (let ([subst* (unify #'τa #'τb
                                  #:src (get-stx-prop/car this-syntax 'constraint-source))])
               (recur (map #{apply-subst subst* %} (rest cs))
                      (compose-substs subst* subst)))]))))

  ; Given a substitution set, recursively walks a syntax object and retroactively replaces ': syntax
  ; properties with their inferred types after unification. Also attaches a ':-string property, which
  ; contains the final value of ': converted to a string using type->string, which is useful for
  ; debugging.
  (define (apply-substitutions-to-types subst stx)
    (define (perform-substitution stx)
      (if (syntax-property stx ':)
          (let ([new-type (apply-subst subst (get-stx-prop/car stx ':))])
            (syntax-property (syntax-property stx ': new-type #t)
                             ':-string (type->string new-type)))
          stx))
    (let recur ([stx stx])
      (syntax-rearm
       (syntax-parse (syntax-disarm stx (current-code-inspector))
         [(elem . rest)
          (perform-substitution
           (datum->syntax this-syntax (cons (recur #'elem) (recur #'rest))
                          this-syntax this-syntax))]
         [_ (perform-substitution this-syntax)])
       stx))))

;; ---------------------------------------------------------------------------------------------------
;; typed forms

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

(define-syntax-parser hash-percent-module-begin
  #:literals [#%plain-module-begin-]
  [(_ . body)
   #:with (#%plain-module-begin- . expanded)
          (local-expand #'(#%plain-module-begin- . body)
                        'module-begin null)
   #:do [(define subst (solve-constraints (collect-constraints #'expanded)))]
   #:with substituted (apply-substitutions-to-types subst #'expanded)
   #'(#%module-begin- . substituted)])

(define-syntax-parser let
  [(_ [x:id val:expr] e:expr)
   #:with [τ_val [] val-] (infer+erase #'val)
   #:do [(define subst (solve-constraints (collect-constraints #'val-)))]
   #:with τ_substituted (apply-subst subst #'τ_val)
   #:with τ_generalized (generalize-type #'τ_substituted)
   #:with val-* (⊢ val- : τ_generalized)
   #:with [τ [x-] e-] (infer+erase #'e #:ctx #'([x : τ_generalized]))
   (⊢ #,(syntax/loc this-syntax
          (let- ([x- val-*]) e-))
      : τ)])

;; ---------------------------------------------------------------------------------------------------
;; primitive operators

(define ((+/c a) b) (+- a b))
(define-syntax + (make-variable-like-transformer
                  (⊢ +/c : (→ Integer (→ Integer Integer)))))
