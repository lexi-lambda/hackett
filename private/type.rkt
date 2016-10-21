#lang curly-fn racket/base

(require racket/require)

(require (for-syntax (multi-in racket [base syntax]))
         (for-template (prefix-in kernel: '#%kernel)
                       racket/base
                       (only-in macrotypes/typecheck
                                get-stx-prop/car
                                set-stx-prop/preserved))
         (multi-in racket [dict format list match syntax])
         (multi-in syntax [id-table parse/define])
         rascal/util/stx
         syntax/parse
         "typerep.rkt")

(provide (all-defined-out)
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
                   (instantiate-type-with τb τvars))))]))

(define current-type-var-environment
  (make-parameter (make-immutable-free-id-table)))

(define (extend-type-var-environment ctx [env (current-type-var-environment)])
  (for/fold ([env env])
            ([(id τ) (in-dict ctx)])
    (free-id-table-set env id τ)))

(define type-free-vars
  (match-lambda
    [(τvar α) (list α)]
    [(base-type _ _) '()]
    [(τapp τa τb) (remove-duplicates (append (type-free-vars τa)
                                             (type-free-vars τb))
                                     free-identifier=?)]))

(define (typeof stx)
  (get-stx-prop/car stx ':))

(define (assign-type stx τ)
  (set-stx-prop/preserved stx ': τ))

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
       (define/syntax-parse [τ-proxy ...] (map property-proxy τs))
       (values
        #`(λ (x- ...)
            (let-syntax ([x (make-variable-like-transformer/thunk
                             (λ (id) (syntax-property
                                      (assign-type #'x- (instantiate-type
                                                         (property-proxy-value #'τ-proxy)))
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
  (values τs xs- stxs-))

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

; Given a type, replaces universally quantified type variables with fresh type variables.
(define instantiate-type
  (match-lambda
    [(∀ αs τ)
     (apply-subst
      (make-immutable-free-id-table
       (for/list ([var (in-list αs)])
         (cons var (fresh var))))
      τ)]
    [τ τ]))

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

; Applies a subsitution set to a type or constraint by recursively replacing all substitutable type
; variables with their substitutions.
(define (apply-subst subst τ)
  (let loop ([τ τ])
    (match τ
      [(τvar α)
       (free-id-table-ref subst α τ)]
      [(∀ αs τ)
       (∀ αs (loop τ))]
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
     stx)))
