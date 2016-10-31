#lang curly-fn racket/base

(require racket/require)

(require (for-syntax (multi-in racket [base syntax]))
         (for-template (prefix-in kernel: '#%kernel)
                       racket/base
                       (only-in macrotypes/typecheck
                                get-stx-prop/car
                                set-stx-prop/preserved))
         (multi-in racket [dict format list match syntax])
         (multi-in syntax [id-set id-table parse/define])
         point-free
         rascal/private/util/stx
         syntax/parse
         "classrep.rkt"
         "typerep.rkt")

(provide (all-defined-out)
         (all-from-out "classrep.rkt")
         (all-from-out "typerep.rkt"))

;; ---------------------------------------------------------------------------------------------------
;; types

(define custom-type-printer-table (make-free-id-table))

(define (register-custom-type-printer! base-type-id printer)
  (free-id-table-set! custom-type-printer-table base-type-id printer))

(define (custom-type-printer base-type-id)
  (free-id-table-ref custom-type-printer-table base-type-id #f))

; Gets the id of the base type in a series of type applications. If the type being applied is not a
; base type, returns #f.
(define applied-base-type-id
  (match-lambda
    [(base-type id _) id]
    [(τapp τ _) (applied-base-type-id τ)]
    [_ #f]))

; Prints a type, potentially consulting custom-type-printer-table for types that should be printed in
; a different way, like →.
(define/match (type->string τ)
  [((τvar α))
   (symbol->string (syntax-e α))]
  [((∀ αs τ))
   (format "(∀ ~a ~a)" (map #{symbol->string (syntax-e %)} αs) (type->string τ))]
  [((τ~ τa τb _))
   (format "(τ~~ ~a ~a)" (type->string τa) (type->string τb))]
  [((⇒ context τ))
   (format "(⇒ ~a ~a)" (map type->string context) (type->string τ))]
  [((has-class (app syntax-local-value (class id _ _ _)) τ))
   (format "(~a ~a)" (syntax-e id) (type->string τ))]
  [({app applied-base-type-id {? values {app custom-type-printer {? values printer}}}})
   (printer τ)]
  [((τapp τf τx))
   (format "(~a ~a)" (type->string τf) (type->string τx))]
  [((base-type id _))
   (symbol->string (syntax-e id))])

; explicitly list all cases instead of having a fallback case to get better error messages when a
; new type representation is added
(define type=?
  (match-lambda**
   [((τvar a) (τvar b))
    (free-identifier=? a b)]
   [((τvar _) _) #f]
   [(_ (τvar _)) #f]
   [((base-type a _) (base-type b _))
    (free-identifier=? a b)]
   [((base-type _ _) _) #f]
   [(_ (base-type _ _)) #f]
   [((τapp τf τx) (τapp τg τy))
    (and (type=? τf τg)
         (type=? τx τy))]
   [((τapp _ _) _) #f]
   [(_ (τapp _ _)) #f]
   [({and τa (∀ αs _)} {and τb (∀ βs _)})
    (and (= (length αs) (length βs))
         (let ([τvars (map fresh αs)])
           (type=? (instantiate-type-with τa τvars)
                   (instantiate-type-with τb τvars))))]
   [((⇒ ctx-a τa) (⇒ ctx-b τb))
    (and (context=? ctx-a ctx-b)
         (type=? τa τb))]
   [((⇒ _ _) _) #f]
   [(_ (⇒ _ _)) #f]
   [((has-class ca τa) (has-class cb τb))
    (and (free-identifier=? ca cb)
         (type=? τa τb))]
   [((has-class _ _) _) #f]
   [(_ (has-class _ _)) #f]))

(define (context=? a b)
  (and (= (length a) (length b))
       (for/and ([pred (in-list a)])
         (member pred b type=?))
       #t))

(define-custom-hash-types type-table type=?)

(define current-type-var-environment
  (make-parameter (make-immutable-free-id-table)))

(define (extend-type-var-environment ctx [env (current-type-var-environment)])
  (for/fold ([env env])
            ([(id τ) (in-dict ctx)])
    (free-id-table-set env id τ)))

(define type-free-vars
  (match-lambda
    [(⇒ ctx τ)
     (remove-duplicates (append (append-map type-free-vars ctx)
                                (type-free-vars τ))
                        free-identifier=?)]
    [(has-class _ τ)
     (type-free-vars τ)]
    [(τvar α) (list α)]
    [(base-type _ _) '()]
    [(τapp τa τb) (remove-duplicates (append (type-free-vars τa)
                                             (type-free-vars τb))
                                     free-identifier=?)]))

(define (typeof stx)
  (get-stx-prop/car stx ':))

(define (assign-type stx τ)
  (match τ
    [(⇒ preds τ)
     (assign-predicates (assign-type stx τ) preds)]
    [τ
     (set-stx-prop/preserved stx ': τ)]))

(define (assign-predicates stx preds)
  (set-stx-prop/preserved stx 'predicates preds))

(define (get-predicates stx)
  (syntax-property stx 'predicates))

(define (collect-predicates stx)
  (collect-properties stx 'predicates))

; Generates a fresh type variable.
(define (fresh [base 'g])
  (τvar (generate-temporary base)))

; Like infers+erase, but for a single syntax object instead of a list.
(define (infer+erase stx #:ctx [ctx '()])
  (define-values [τs xs- stxs-]
    (infers+erase (list stx) #:ctx ctx))
  (values (first τs) xs- (first stxs-)))

; Like define/infers+erase, but with the single syntax object behavior of infer+erase.
(define-simple-macro (define/infer+erase [τ xs-pat stx-pat] args ...)
  #:with xs-tmp (generate-temporary #'xs-pat)
  #:with stx-tmp (generate-temporary #'stx-pat)
  (begin
    (match-define-values [τ xs-tmp stx-tmp] (infer+erase args ...))
    (define/syntax-parse xs-pat xs-tmp)
    (define/syntax-parse stx-pat stx-tmp)))

; The main inference function. Expands all of stxs within the context of ctx. This function does
; three main things:
;
;  1. It invokes local-expand on each of the syntax objects provided to it. Before calling
;     local-expand, it binds each of the identifiers in ctx to a syntax transformer that expands
;     to a reference to a fresh location, with the type provided in ctx attached as a syntax
;     property.
;
;  2. After expansion, it collects the types of the resulting syntax objects into a list.
;     Additionally, it collects the identifiers used to create fresh locations into a list, which
;     must be put in scope by the caller of infers+erase so that they are accessible by the bodies.
;
;     These three things (expanded syntax objects, result types, and fresh identifiers) are returned
;     from infers+erase as three return values, in the following order:
;
;       (values types fresh-ids expanded-stxs)
;
;  3. Finally, infers+erase also automatically attaches disappeared-use and disappeared-binding
;     syntax properties as necessary in order to cooperate with Check Syntax. (This is necessary
;     since the identifiers used in the source syntax are erased and replaced with the generated
;     fresh locations mentioned earlier.)
;
;    (listof syntax?)
;    (listof (cons/c identifier? type?))
; -> (values (listof type?)
;            (listof identifier?)
;            (listof syntax?))
(define (infers+erase stxs #:ctx [ctx '()])
  (cond
    [(empty? stxs)
     (values '() '() '())]
    [else
     (define-values [wrapped-stx disappeared-bindings]
       (match ctx
         [(list (cons xs τs) ...)
          (define/syntax-parse [x ...] xs)
          (define/syntax-parse [x- ...]
            (for/list ([x-stx (in-list xs)])
              (let ([tmp (generate-temporary x-stx)])
                (propagate-original-for-check-syntax
                 (syntax-local-introduce x-stx)
                 (datum->syntax tmp (syntax-e tmp) x-stx x-stx)))))
          (define/syntax-parse [x-introduced ...] (map syntax-local-introduce (attribute x-)))
          (define/syntax-parse [τ-expr ...] (map preservable-property->expression τs))
          (values
           #`(λ (x- ...)
               (let-syntax ([x (make-variable-like-transformer/thunk
                                (λ (id) (syntax-property
                                         (assign-type #'x- (instantiate-type τ-expr))
                                         'disappeared-use
                                         (list (propagate-original-for-check-syntax
                                                (syntax-local-introduce id)
                                                (datum->syntax #'x-introduced
                                                               (syntax-e #'x-introduced)
                                                               id id))))))]
                            ...)
                 #,@stxs))
           (attribute x-))]))
     (define-values [τs xs- stxs-]
       (syntax-parse (local-expand wrapped-stx 'expression null)
         #:literals [kernel:lambda kernel:let-values]
         [(kernel:lambda xs-
                         (kernel:let-values _
                                            (kernel:let-values _ bodies ...)))
          (values (map typeof (attribute bodies)) #'xs-
                  (map #{syntax-property % 'disappeared-binding disappeared-bindings}
                       (attribute bodies)))]))
     (values τs xs- stxs-)]))

; A helper macro for making it easier to consume the results of infers+erase. Since infers+erase
; produces three values, two of which are syntax, it is useful to bind the syntax values to pattern
; variables that cooperate with `syntax`, which this macro automatically does. Additionally, it
; binds the single value result, the types, in a position that accepts `match` patterns.
(define-simple-macro (define/infers+erase [τs xs-pat stxs-pat] args ...)
  #:with xs-tmp (generate-temporary #'xs-pat)
  #:with stxs-tmp (generate-temporary #'stxs-pat)
  (begin
    (match-define-values [τs xs-tmp stxs-tmp] (infers+erase args ...))
    (define/syntax-parse xs-pat xs-tmp)
    (define/syntax-parse stxs-pat stxs-tmp)))

(define instantiate-type/subst
  (match-lambda
    [(∀ αs τ)
     (let ([subst (make-immutable-free-id-table
                   (for/list ([var (in-list αs)])
                     (cons var (fresh var))))])
       (values (apply-subst subst τ) subst))]
    [τ (values τ empty-subst)]))

; Given a type, replaces universally quantified type variables with fresh type variables.
(define (instantiate-type τ)
  (match-define-values [τ_inst _] (instantiate-type/subst τ))
  τ_inst)

; Instantiates a type with a particular set of type variables. It is the responsibility of the
; caller to ensure the provided type variables are unique.
(define (instantiate-type-with τ τvars)
  (match τ
    [(∀ αs τ)
     (unless (= (length αs) (length τvars))
       (raise-arguments-error 'instantiate-type-with
                              (~a "the number of provided type variables does not match the number "
                                  "of quantified type variables in the provided type")
                              "τ" τ
                              "τvars" τvars))
     (apply-subst
      (make-immutable-free-id-table
       (for/list ([α (in-list αs)]
                  [τvar (in-list τvars)])
         (cons α τvar)))
      τ)]))

; Given a type, finds all free type variables and universally quantifies them using ∀.
(define (generalize-type τ)
  (let ([free-vars (type-free-vars τ)])
    (if (empty? free-vars) τ
        (∀ free-vars τ))))

;; ---------------------------------------------------------------------------------------------------
;; typeclasses

(define (make-class id method-table method-types-quantified-id)
  (class id method-table method-types-quantified-id (make-mutable-type-table)))

; Gets the method table for a class, but with all of the types specialized for a particular instance.
; For example, for (Show Bool), this would produce a table like this:
;
;   show : (∀ [] (⇒ [] (→ Bool String)))
;
; For instances with additional predicates, those predicates will be moved into the resulting types.
; For example, the table for (Show (Maybe α)) would look like this:
;
;   show : (∀ [α] (⇒ [(Show α)] (→ (Maybe α) String)))
;
; For this reason, the provided τ_instance should be the full type scheme rather than a plain type.
(define (class-method-table/instantiate class τ_instance)
  (match-let* ([(∀ αs_instance (⇒ preds_instance τ_instance)) τ_instance]
               [method-table (class-method-table class)]
               [quantified-id (class-method-types-quantified-id class)])
    (define instantiate-class-method
      (match-lambda
        [(∀ αs (⇒ preds τ))
         (let* (; first, remove the class predicate (e.g. (Show a) if the class is Show)
                [type-without-class-pred
                 (⇒ (append (remove (has-class (class-id class) (τvar quantified-id)) preds type=?)
                            preds_instance)
                    τ)]
                ; next, instantiate the type variable with the provided instance
                [instantiated-type
                 (instantiate-type-with (∀ (list quantified-id) type-without-class-pred)
                                        (list τ_instance))]
                ; finally, remove the type variable from the quantified list
                [type-without-quantified-id
                 (∀ (append (remove quantified-id αs free-identifier=?)
                            αs_instance)
                    instantiated-type)])
           type-without-quantified-id)]))
    (make-immutable-free-id-table
     (for/list ([(id τ) (in-free-id-table method-table)])
       (cons id (instantiate-class-method τ))))))

(define (register-class-instance! class τ instance #:src src)
  (let ([instances (class-instances class)])
    (for ([τold (in-dict-keys instances)])
      (assert-no-instance-overlap! τ τold #:src src))
    (dict-set! instances τ instance)))

(define (assert-no-instance-overlap! τnew τold #:src src)
  (or (with-handlers ([exn:fail:syntax? void])
        (unify τnew τold #:src src)
        #f)
      (raise-syntax-error #f (~a "instance " (type->string τnew) " overlaps "
                                 "with " (type->string τold))
                          src)))

; Given a class constraint, finds an instance that matches, then returns a list of additional
; constraints that need to be satisfied. For a simple instance, like (Show Bool), this will return an
; empty list, but for more complex ones, like (∀ [α] (⇒ [(Show α)] (Maybe α))), it will return the
; list of required constraints.
(define (pred->instance+preds pred)
  (match-let* ([(has-class class-id τ) pred]
               [class (syntax-local-value class-id)]
               [instances (class-instances class)])
    (for/or ([(instance-τ instance) (in-dict instances)])
      (match-let* ([(⇒ ctx* τ*) (instantiate-type instance-τ)]
                   [subst (unify/one-way τ* τ)])
        (and subst (list instance (map #{apply-subst subst %} ctx*)))))))

; Like pred->instance+preds, but only returns the additional constraints.
(define (matching-instance-context pred)
  (and~> (pred->instance+preds pred) second))

; Given a list of has-class predicates and a single has-class predicate, determines if the latter can
; be deduced if all of the former are true.
(define (entails? ctx pred)
  (or (and (member pred ctx type=?) #t)
      (let ([new-preds (matching-instance-context pred)])
        (and new-preds (andmap #{entails? ctx %} new-preds)))))

(define pred-head-normal-form?
  (match-lambda
    [(has-class _ τ)
     (let loop ([τ τ])
       (match τ
         [(τvar _)       #t]
         [(? base-type?) #f]
         [(τapp τ _)     (loop τ)]))]))

(define (pred->head-normal-form pred)
  (if (pred-head-normal-form? pred)
      (list pred)
      (let ([new-preds (matching-instance-context pred)])
        (unless new-preds
          (raise-syntax-error 'pred->head-normal-form (~a "could not deduce " (type->string pred))))
        (append-map pred->head-normal-form new-preds))))

(define (simplify-context ctx)
  (let loop ([ctx ctx]
             [preserved '()])
    (if (empty? ctx) preserved
        (let ([pred (first ctx)]
              [ctx* (rest ctx)])
          (if (entails? (append preserved ctx*) pred)
              (loop ctx* preserved)
              (loop ctx* (cons pred preserved)))))))

(define (reduce-context ctx)
  (simplify-context (append-map pred->head-normal-form ctx)))

; Given a piece of syntax with a set of typeclass constraints, wrap it such that it accepts typeclass
; dictionaries and passes them to invocations that need them.
(define (erase-typeclasses stx preds #:existing-dict-mapping [dict-mapping '()])
  (let* ([existing-preds (map car dict-mapping)]
         ; only demand fresh dictionaries for preds not in the existing dict-mapping
         [missing-preds (filter-not #{member % existing-preds type=?} preds)]
         [dict-ids (generate-temporaries missing-preds)]
         ; combine the new id mapping and the existing id mapping
         [total-dict-mapping (append dict-mapping (map cons missing-preds dict-ids))]
         ; replace constrained application with application that will supply dictionaries
         [stx* (insert-dictionary-uses stx total-dict-mapping)])
    ; wrap the piece of syntax with lambdas as necessary
    (for/fold ([stx stx*])
              ([dict-id (in-list (reverse dict-ids))])
      #`(λ (#,dict-id) #,stx))))

(define (insert-dictionary-uses stx dict-mapping)
  (define (make-dictionary-application stx preds)
    (let loop ([stx stx]
               [preds preds])
      (if (empty? preds) stx
          (match-let ([{list* pred preds} preds])
            (if (τvar? (has-class-τ pred))
                (let ([mapping (assoc pred dict-mapping type=?)])
                  (unless mapping
                    (error 'insert-dictionary-uses
                           "internal error: no dictionary for ~a\n  in mapping: ~a"
                           (type->string pred) dict-mapping))
                  (loop #`(#,stx #,(cdr mapping)) preds))
                (match-let* ([{list instance preds*} (pred->instance+preds pred)]
                             [dict-id (instance-dict-id instance)]
                             [dict-stx (loop dict-id preds*)])
                  (loop #`(#,stx #,dict-stx) preds)))))))
  (let loop ([stx stx])
    (syntax-parse stx
      #:context 'replace-method-stubs
      [_
       #:do [(define preds (get-predicates this-syntax))]
       #:when preds
       preds
       (make-dictionary-application this-syntax preds)]
      [(a . b)
       (datum->syntax this-syntax (cons (loop #'a) (loop #'b)) this-syntax this-syntax)]
      [_ this-syntax])))

;; ---------------------------------------------------------------------------------------------------
;; constraints & substitution

; Attaches a constraint to a syntax object by associating a type with the 'constraint syntax
; property.
(define (assign-constraint stx τa τb)
  (syntax-property stx 'constraints (list (τ~ τa τb stx)) #t))

; Like assign-constraint, but accepts a list of pairs and produces a set of constraints instead of a
; single contraint.
(define (assign-constraints stx τ-pairs #:existing-constraints [existing-cs '()])
  (syntax-property stx 'constraints
                   (append (map #{τ~ (car %) (cdr %) stx} τ-pairs)
                           existing-cs)
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

; Performs a symmetric merge of two substitution sets, ensuring that the substitutions agree for all
; duplicate keys. If they do not, merge-substs returns #f. (Used by unify/one-way.)
(define (merge-substs a b)
  (and (for/and ([k (in-free-id-set
                     (free-id-set-intersect (immutable-free-id-set (free-id-table-keys a))
                                            (immutable-free-id-set (free-id-table-keys b))))])
         (type=? (free-id-table-ref a k)
                 (free-id-table-ref b k)))
       (free-id-table-union a b)))

; Applies a subsitution set to a type or constraint by recursively replacing all substitutable type
; variables with their substitutions.
(define (apply-subst subst τ)
  (let loop ([τ τ])
    (match τ
      [(τvar α)
       (free-id-table-ref subst α τ)]
      [(∀ αs τ)
       (∀ αs (loop τ))]
      [(⇒ ctx τ)
       (⇒ (map loop ctx) (loop τ))]
      [(has-class class τ)
       (has-class class (loop τ))]
      [(τapp τf τx)
       (τapp (loop τf) (loop τx))]
      [(base-type _ _)
       τ]
      [(τ~ a b src)
       (τ~ (loop a) (loop b) src)])))

; Attempts to unify the two provided types, reporting errors in terms of the provided source syntax
; object.
(define (unify τa τb #:src src)
  (if (type=? τa τb)
      empty-subst
      (match* (τa τb)
        [((⇒ _ τa) τb)
         (unify τa τb #:src src)]
        [(τa (⇒ _ τb))
         (unify τa τb #:src src)]
        [((τvar α) τ)
         (bind-subst α τ)]
        [(τ (τvar α))
         (bind-subst α τ)]
        [((τapp τa τb) (τapp τc τd))
         (unify* (list (cons τa τc)
                       (cons τb τd))
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
       (compose-substs subst* subst))]))

; Attempts to unify the first type with the second one, leaving the second type unchanged. Unlike
; unify, if unify/one-way fails, it returns #f. (Used by entailment.)
(define (unify/one-way τa τb)
  (if (type=? τa τb)
      empty-subst
      (match* (τa τb)
        [((τapp τa τb) (τapp τc τd))
         (let ([subst-a (unify/one-way τa τc)]
               [subst-b (unify/one-way τb τd)])
           (and subst-a subst-b
                (merge-substs subst-a subst-b)))]
        [((τvar α) τ)
         (bind-subst α τ)]
        [(_ _) #f])))

; Given a set of constraints, attempts to solve them with unification.
(define (solve-constraints cs)
  (let loop ([cs cs]
             [subst empty-subst])
    (if (empty? cs) subst
        (match (first cs)
          [(τ~ τa τb src)
           (let ([subst* (unify τa τb #:src src)])
             (loop (map #{apply-subst subst* %} (rest cs))
                   (compose-substs subst* subst)))]))))

; Given a substitution set, recursively walks a syntax object and retroactively replaces ': syntax
; properties with their inferred types after unification. Also attaches a ':-string property, which
; contains the final value of ': converted to a string using type->string, which is useful for
; debugging.
(define (apply-substitutions-to-types subst stx)
  (define (perform-substitution/: stx)
    (if (syntax-property stx ':)
        (let ([new-type (apply-subst subst (get-stx-prop/car stx ':))])
          (syntax-property (syntax-property stx ': new-type #t)
                           ':-string (type->string new-type)))
        stx))
  (define (perform-substitution/preds stx)
    (if (syntax-property stx 'predicates)
        (let ([new-preds (map #{apply-subst subst %} (syntax-property stx 'predicates))])
          (syntax-property stx 'predicates new-preds #t))
        stx))
  (define (perform-substitution stx)
    (perform-substitution/preds (perform-substitution/: stx)))
  (let recur ([stx stx])
    (syntax-rearm
     (syntax-parse (syntax-disarm stx (current-code-inspector))
       [(elem . rest)
        (perform-substitution
         (datum->syntax this-syntax (cons (recur #'elem) (recur #'rest))
                        this-syntax this-syntax))]
       [_ (perform-substitution this-syntax)])
     stx)))
