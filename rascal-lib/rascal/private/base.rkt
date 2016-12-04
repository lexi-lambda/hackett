#lang curly-fn racket/base

(require racket/require)

(require (for-syntax (multi-in racket [base dict format function list match splicing syntax])
                     (multi-in rascal/private [type util/stx])
                     (multi-in syntax/parse [class/local-value class/paren-shape define
                                             experimental/specialize experimental/template])
                     (only-in srfi/1 list-index)
                     macrotypes/stx-utils
                     point-free
                     syntax/id-table)
         (for-meta 2 racket/base
                     syntax/transformer)
         (only-in macrotypes/typecheck postfix-in type-error)
         (postfix-in - (multi-in racket [base format]))
         syntax/id-table
         syntax/parse/define)

(provide (for-syntax (all-defined-out)
                     (all-from-out rascal/private/type))
         (all-defined-out))

;; ---------------------------------------------------------------------------------------------------
;; type constructors

(begin-for-syntax
  (define (literal-transformer stx)
    (let ([id (syntax-parse stx
                [(id:id . _) #'id]
                [id:id       #'id])])
      (raise-syntax-error #f "cannot be used as an expression" id))))

(define-syntax ∀ literal-transformer)
(define-syntax ⇒ literal-transformer)
(define-syntax ← literal-transformer)

(define-syntax-parser define-base-type
  [(_ τ:id
      {~or {~optional {~seq #:constructors constructors:expr}
                      #:defaults ([constructors #'#f])}
           other-option}
      ...)
   #'(begin
       (define-syntax τ (base-type #'τ constructors))
       (begin-for-syntax
         (define-base-type τ #:constructors constructors other-option ...)))])

(define-base-type → #:arity 2)
(define-base-type Integer)
(define-base-type String)

(begin-for-syntax
  ; a → type constructor that supports multiple arguments
  (define →/curried
    (match-lambda*
      [(list τa τb)
       (→ τa τb)]
      [(list τ τs ..2)
       (→ τ (apply →/curried τs))]))

  ; like →/curried, but interprets (→ τ) as τ
  (define →/curried*
    (match-lambda*
      [(list τ) τ]
      [other (apply →/curried other)]))

  (register-custom-type-printer!
   #'→ (match-lambda
         [(→ τa τb)
          (format "(→ ~a ~a)" (type->string τa) (type->string τb))])))

;; ---------------------------------------------------------------------------------------------------
;; types

(begin-for-syntax
  (define-syntax-class/specialize local-value/class
    (local-value class? #:failure-message "identifier was not bound to a class"))

  (define (type-eval stx #:ctx [ctx '()])
    (parameterize ([current-type-var-environment (extend-type-var-environment ctx)])
      (let loop ([stx stx])
        (syntax-parse stx
          #:context 'type-eval
          #:literals [∀ ⇒]
          ; infix application (curly braces)
          [{~braces a op b {~seq ops bs} ...+}
           (loop (template
                  {{a op b} (?@ ops bs) ...}))]
          [{~braces ~! a op b}
           (loop #'((op a) b))]
          ; normal type evaluation
          [τ:id
           (or (free-id-table-ref (current-type-var-environment) #'τ #f)
               (syntax-local-value #'τ))]
          [(∀ ~! [α:id ...] {~optional {~seq (class-id:local-value/class τ_pred) ... ⇒}
                                       #:defaults ([[class-id 1] '()]
                                                   [[τ_pred   1] '()])}
              τ)
           #:do [; handle ∀
                 (define α-types (map fresh (attribute α)))
                 (define α-ids (map τvar-id α-types))
                 (define ctx (map cons (attribute α) α-types))
                 (define τ* (type-eval #'τ #:ctx ctx))
                 ; call type-free-vars to get the order the type variables appear in τ; this assures
                 ; they will have a canonical order, which allows type=? to work more easily
                 (define α-ids* (filter #{member % α-ids free-identifier=?}
                                        (type-free-vars τ*)))

                 ; handle ⇒
                 (define τ_preds (map #{type-eval % #:ctx ctx} (attribute τ_pred)))
                 (define preds (map has-class (attribute class-id) τ_preds))]
           (∀ α-ids* (⇒ preds τ*))]
          [(τ a)
           (τapp (loop #'τ)
                 (loop #'a))]
          [(τ a as ...)
           (loop #'((τ a) as ...))]))))

  (define-simple-macro (⊢ e {~literal :} τ)
    (assign-type #`e (type-eval #`τ))))

;; ---------------------------------------------------------------------------------------------------
;; general typed forms

(begin-for-syntax
  ; (listof identifier?) (listof type?) (listof syntax?)
  ; -> (or/c (list (listof type?) (listof identifier?) (listof syntax?))
  (define (typecheck-annotated-bindings xs τs_annotated exprs
                                        #:body [body #f]
                                        #:existing-dict-mapping [dict-mapping '()])
    ; run the typechecker
    (define-values [τs_inferred xs- exprs- τ_body body-]
      (let ([ctx (map cons xs τs_annotated)])
        (if body
            (let-values ([(τs xs- vals-) (infers+erase (cons body exprs) #:ctx ctx)])
              (values (rest τs) xs- (rest vals-) (first τs) (first vals-)))
            (let-values ([(τs xs- vals-) (infers+erase exprs #:ctx ctx)])
              (values τs xs- vals- #f #f)))))

    ; solve constraints and apply the resulting substitutions
    (define-values [annotation-constraints annotation-substs]
      (for/lists [constraints substs]
                 ([τ_annotated (in-list τs_annotated)]
                  [τ_inferred (in-list τs_inferred)]
                  [expr (in-list exprs)])
        (match-let*-values ([(τ_normalized) (type->normalized-scheme τ_annotated)]
                            ; TODO: actually validate that the preds in annotations are valid
                            [((⇒ _ τ) subst) (instantiate-type/subst τ_normalized)])
          (values (τ~ τ τ_inferred expr) subst))))
    (define subst (solve-constraints (append (collect-constraints (datum->syntax #f exprs-))
                                             annotation-constraints)))
    (define τs_substituted (map #{apply-subst subst %} τs_inferred))
    (define τ_body_substituted (and~> τ_body #{apply-subst subst %}))
    (define dict-mappings-substituted
      (for/list ([annotation-subst (in-list annotation-substs)])
        (for/list ([mapping (in-list dict-mapping)])
          (cons (apply-subst subst (apply-subst annotation-subst (car mapping)))
                (cdr mapping)))))

    ; collect predicates and apply the substitutions to those, too, then typecheck them
    (define predicatess (map collect-predicates exprs-))
    (define substituted-predicatess (map #{map #{apply-subst subst %} %} predicatess))
    (define reduced-predicatess
      (for/list ([predicates (in-list substituted-predicatess)])
        (reduce-context predicates)))

    ; generalize the resulting types, apply the results to the original syntax and return everything
    (define τs_generalized (map #{generalize-type %1 #:src %2}
                                (map ⇒ reduced-predicatess τs_substituted)
                                exprs))
    (let ([vals-generalized
           (for/list ([expr- (in-list exprs-)]
                      [τ (in-list τs_generalized)]
                      [preds (in-list reduced-predicatess)]
                      [dict-mapping (in-list dict-mappings-substituted)])
             (~> (apply-substitutions-to-types subst expr-)
                 #{erase-typeclasses % preds #:existing-dict-mapping dict-mapping}
                 #{assign-type % τ}))])
      (if body
          (list τs_generalized xs- vals-generalized τ_body_substituted body-)
          (list τs_generalized xs- vals-generalized)))))

(define-syntax (def stx) (raise-syntax-error #f "can only be used at the top level of a module" stx))

(define-syntax-parser λ1
  [(_ x:id e:expr)
   #:do [(define τv (fresh))
         (define/infer+erase [τ [x-] e-] #'e #:ctx (list (cons #'x τv)))]
   (assign-type #'(λ- (x-) e-)
                (→ τv τ))])

(define-syntax-parser λ
  [(_ (x:id) e:expr)
   #'(λ1 x e)]
  [(_ (x:id xs:id ...) e:expr)
   #'(λ1 x (λ (xs ...) e))])

(define-syntax-parser hash-percent-app1
  [(_ fn arg)
   #:do [(define τv (fresh))
         (define/infer+erase [τ_fn [] fn-] #'fn)
         (define/infer+erase [τ_arg [] arg-] #'arg)]
   (assign-constraint (assign-type (syntax/loc this-syntax
                                     (#%app- fn- arg-))
                                   τv)
                      τ_fn (→ τ_arg τv))])

(define-syntax-parser hash-percent-app
  ; infix application (curly braces)
  [{~braces app a op b {~seq ops bs} ...+}
   (template
    {app {app a op b} (?@ ops bs) ...})]
  [{~braces ~! app a op b}
   (syntax-property #'(app (app op a) b)
                    'paren-shape #f)]
  ; prefix application
  [(_ fn arg)
   (syntax/loc this-syntax
     (hash-percent-app1 fn arg))]
  [(_ fn arg args ...+)
   (quasisyntax/loc this-syntax
     (hash-percent-app #,(syntax/loc this-syntax
                           (hash-percent-app1 fn arg))
                       args ...))])

(define-syntax-parser hash-percent-datum
  [(_ . n:integer)
   (⊢ (#%datum- . n) : Integer)]
  [(_ . n:str)
   (⊢ (#%datum- . n) : String)]
  [(_ . x)
   (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)])

(define-syntax-parser hash-percent-module-begin
  #:literals [def]
  [(_ {~seq {~or {~seq {~seq {~and definition (def . _)} ...+}
                       {~seq {~and other-form {~not (def . _)}} ...}}
                 {~seq {~seq {~and definition (def . _)} ...}
                       {~seq {~and other-form {~not (def . _)}} ...+}}}}
      ...)
   (template
    (#%plain-module-begin-
     (?@ (top-level-definitions definition ...)
         other-form ...)
     ...))])

(define-syntax-parser top-level-definitions
  #:literals [: def]
  [(_ (def x:id : τ-ann expr) ...)
   #:do [(match-define {list τs xs- vals-}
           (typecheck-annotated-bindings (attribute x)
                                         (map type-eval (attribute τ-ann))
                                         (attribute expr)))]
   #:with [[τ-expr ...] [x- ...] [val- ...]]
          (list (map preservable-property->expression τs) xs- vals-)
   #'(begin-
      (define- x- val-) ...
      (define-syntax x
        (make-variable-like-transformer/thunk
         (λ (stx) (assign-type #'x- (instantiate-type τ-expr)))))
      ...)])

(define-syntax-parser let1
  [(_ [x:id val:expr] e:expr)
   #:do [(define/infer+erase [τ_val [] val-] #'val)
         (define subst (solve-constraints (collect-constraints #'val-)))
         (define τ_substituted (apply-subst subst τ_val))
         (define τ_generalized (generalize-type τ_substituted #:src #'val))]
   #:with val-* (assign-type #'val- τ_generalized)
   #:do [(define/infer+erase [τ [x-] e-] #'e #:ctx (list (cons #'x τ_generalized)))]
   (assign-type (syntax/loc this-syntax
                  (let- ([x- val-*]) e-))
                τ)])

(define-syntax-parser let
  [(_ () e:expr)
   #'e]
  [(_ ([x:id val:expr] [xs:id vals:expr] ...) e:expr)
   #'(let1 [x val]
       (let ([xs vals] ...)
         e))])

(define-syntax-parser :
  [(_ e:expr τ-expr)
   #:do [(define τ (type-eval #'τ-expr))
         (define/infer+erase [τ_inferred [] e-] #'e)]
   (assign-constraint (assign-type #'e- τ) τ τ_inferred)])

(define-syntax-parser letrec
  #:literals [:]
  [(_ ([x:id : τ-ann val:expr] ...) body:expr)
   #:do [(match-define {list _ xs- vals- τ_body body-}
           (typecheck-annotated-bindings (attribute x)
                                         (map type-eval (attribute τ-ann))
                                         (attribute val)
                                         #:body #'body))]
   #:with [[x- ...] [val- ...] body-] (list xs- vals- body-)
   (assign-type (syntax/loc this-syntax
                  (letrec- ([x- val-] ...) body-))
                τ_body)])

;; ---------------------------------------------------------------------------------------------------
;; typeclasses

(define (method-stub . _)
  (error 'method-stub "should never be called"))

(begin-for-syntax
  ; TODO: move this somewhere else and make types vs quantified types vs schemes more disciplined
  (define type->normalized-scheme
    (match-lambda
      [{and τ (∀ _ (⇒ _ _))}
       τ]
      [(∀ αs τ)
       (∀ αs (⇒ '[] τ))]
      [{and τ (⇒ _ _)}
       (∀ '[] τ)]
      [τ
       (∀ '[] (⇒ '[] τ))])))

(define-syntax-parser class
  #:literals [:]
  [(_ (id:id α:id) [method:id : τ_method-ann] ...)
   #:do [(define τvar (fresh #'α))]
   #:with α* (τvar-id τvar)
   #'(begin-
       (define-syntax id (make-class #'id (make-free-id-table) #'α*))
       (define-class-method! (id α α*) method τ_method-ann) ...)])

(define-syntax-parser define-class-method!
  [(_ (class-id:local-value/class α:id α*:id) method:id τ_method-ann)
   #:do [; create the method type
         (define class-var (τvar #'α*))
         (define τ_method (type-eval #'τ_method-ann #:ctx (list (cons #'α class-var))))
         (define τ_method*
           ; extend the existing list of quantified vars and preds
           (match-let ([(∀ αs (⇒ ctx τ)) (type->normalized-scheme τ_method)])
             (∀ (cons #'α* αs)
                (⇒ (cons (has-class #'class-id class-var) ctx) τ))))]
   #:with method-impl (generate-temporary #'method)
   #:with τ_method-expr (preservable-property->expression τ_method*)
   #'(begin-
       ; register the class method in the table in a begin-for-syntax block so that the side-effect is
       ; re-executed for importing modules
       (begin-for-syntax-
         (syntax-parse (quote-syntax class-id)
           [class-id*:local-value/class
            (let* ([class (attribute class-id*.local-value)]
                   [method-table (class-method-table class)])
              (free-id-table-set! method-table #'method τ_method-expr))]))
       ; define the method and the implementation that will defer to a dictionary
       (define- (method-impl dict) (free-id-table-ref dict #'method))
       (define-syntax method
         (make-variable-like-transformer/thunk
          (λ (stx) (assign-type (syntax/loc stx method-impl)
                                (instantiate-type τ_method-expr))))))])

(begin-for-syntax
  (define-syntax-class instance-spec
    #:attributes [class type]
    #:literals [∀ ⇒]
    [pattern (∀ αs pred ... ⇒ ~! (id:local-value/class τ))
             #:attr class (attribute id.local-value)
             #:attr type (type-eval #'(∀ αs pred ... ⇒ τ))]
    [pattern (∀ ~! αs (id:local-value/class τ))
             #:attr class (attribute id.local-value)
             #:attr type (type->normalized-scheme (type-eval #'(∀ αs τ)))]
    [pattern (id:local-value/class τ)
             #:attr class (attribute id.local-value)
             #:attr type (type->normalized-scheme (type-eval #'(∀ [] τ)))]))

(define-syntax-parser instance
  [(_ spec:instance-spec [method:id impl] ...)
   #:with dict-id (generate-temporary 'dict)
   #:with [specialized-method ...] (generate-temporaries (attribute method))
   #:do [(match-define (∀ _ (⇒ dict-preds _)) (attribute spec.type))
         (define dict-pred-ids (generate-temporaries dict-preds))]
   #:do [(define (app/dict-preds stx)
           (for/fold ([stx stx])
                     ([pred-id (in-list dict-pred-ids)])
             #`(#,stx #,pred-id)))]
   #:with [specialized-method-sig ...] (map app/dict-preds (attribute specialized-method))
   #`(begin-
       ; register the class in a begin-for-syntax block so that the side-effect is re-executed for
       ; importing modules
       (begin-for-syntax-
         (syntax-parse (quote-syntax spec)
           [spec*:instance-spec
            (let ([class (attribute spec*.class)])
              (register-class-instance! class
                                        (attribute spec*.type)
                                        (instance #'dict-id)
                                        #:src (quote-syntax #,this-syntax)))]))

       ; define the instance method implementations themselves
       (define-instance-method spec method specialized-method impl) ...
       ; define a dictionary and store references to the instance methods
       (define- #,(app/dict-preds #'dict-id)
         (make-immutable-free-id-table
          (list- (cons- #'method specialized-method-sig) ...))))])

(define-syntax-parser define-instance-method
  [(_ spec:instance-spec method:id specialized-method:id impl)
   #:do [(define class (attribute spec.class))

         ; generate ids and a mapping for the dictionaries in the instance context
         (match-define (∀ _ (⇒ dict-preds _)) (attribute spec.type))
         (define dict-pred-ids (generate-temporaries dict-preds))
         (define dict-mapping (map cons dict-preds dict-pred-ids))

         ; actually do the typechecking against the type signature from the class
         (define method-table (class-method-table/instantiate class (attribute spec.type)))
         (define τ_method (free-id-table-ref method-table #'method))
         (match-define {list _ _ {list impl-}}
           (typecheck-annotated-bindings (list #'specialized-method)
                                         (list τ_method)
                                         (list #'impl)
                                         #:existing-dict-mapping dict-mapping))

         ; bind the dictionary ids from the instance context
         (define (app/dict-preds stx)
           (for/fold ([stx stx])
                     ([pred-id (in-list dict-pred-ids)])
             #`(#,stx #,pred-id)))]
   #:with impl- impl-
   #:with specialized-method-sig (app/dict-preds #'specialized-method)
   #'(define- specialized-method-sig impl-)])
