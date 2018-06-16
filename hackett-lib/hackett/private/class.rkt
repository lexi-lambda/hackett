#lang curly-fn racket/base

(require racket/require hackett/private/type-reqprov hackett/private/util/require

         (for-syntax (multi-in racket [base format list match set string syntax])
                     (multi-in syntax/parse [class/local-value experimental/template])
                     syntax/id-set
                     syntax/id-table
                     threading)
         (postfix-in - (combine-in racket/base
                                   syntax/id-table))
         syntax/parse/define

         (for-syntax hackett/private/infix)
         (except-in hackett/private/base @%app)
         (only-in (unmangle-types-in #:no-introduce (only-types-in hackett/private/kernel))
                  ∀ => -> [#%app @%app]))

(provide (for-syntax class-id)
         class instance derive-instance)

(begin-for-syntax
  (define-syntax-class (class-id #:require-deriving-transformer? [require-deriving-transformer? #f])
    #:description "class id"
    #:attributes [local-value]
    [pattern
     {~var || (local-value class:info? #:failure-message "identifier was not bound to a class")}
     #:fail-unless (or (not require-deriving-transformer?)
                       (class:info-deriving-transformer (attribute local-value)))
                   "class is not derivable"]))

(define-syntax-parser class
  #:literals [: => -> let-values #%plain-app]
  [(_ {~optional {~seq {~type constr} ... {~type =>/use:=>}} #:defaults ([[constr 1] '()])}
      {~type (name:id var-id:id ...)}
      {~optional {~seq #:fundeps {~type [[{~and {~not ->} fundep-lhs:id} ...+
                                          ->/use:-> {~and {~not ->} fundep-rhs:id} ...+]
                                         ...]}}
                 #:defaults ([[fundep-lhs 2] '()] [[fundep-rhs 2] '()] [[->/use 1] '()])}
      [method-id:id
       {~or {~once {~seq {~and : {~var :/use}} {~type bare-t}}}
            {~optional fixity:fixity-annotation}}
       ...
       {~optional method-default-impl:expr}]
      ...
      {~optional {~seq #:deriving-transformer deriving-transformer:expr}
                 #:defaults ([deriving-transformer #'#f])})
   #:fail-when (for*/or ([fundep-vars (in-sequences (in-list (attribute fundep-lhs))
                                                    (in-list (attribute fundep-rhs)))]
                         [fundep-var (in-list fundep-vars)])
                 (and (not (member fundep-var (attribute var-id) bound-identifier=?))
                      fundep-var))
               "non-class variable in functional dependency specification"

   ; The methods in a class’s method table should *not* be quantified. That is, in this class:
   ;
   ;    (class (Show a)
   ;      [show : {a -> a}])
   ;
   ; The type for show stored in the method table should be {a -> a}, not
   ; (∀ [a] (Show a) => {a -> a}). However, in order to expand the user-provided {a -> a} type in
   ; a context where ‘a’ is bound, we need to bind it into a definition context before expanding it.
   ; We also want to expand superclass constraints in the same context so that the same variable is
   ; bound in both situations.
   #:do [(define t-intdef-ctx (syntax-local-make-definition-context))]
   #:with [[var-id- ...] [[fundep-lhs- ...] [fundep-rhs- ...]] ...]
          (internal-definition-context-introduce
           t-intdef-ctx
           #'[[var-id ...] [[fundep-lhs ...] [fundep-rhs ...]] ...])
   #:do [(syntax-local-bind-syntaxes (attribute var-id) #f t-intdef-ctx)]

   #:with [(~var method-t (type t-intdef-ctx)) ...] (attribute bare-t)
   #:with [(~var super-constr (type t-intdef-ctx)) ...] (attribute constr)
   
   #:with [method-id- ...] (generate-temporaries #'[method-id ...])
   #:attr [method-default-id- 1] (map #{and %1 %2}
                                      (attribute method-default-impl)
                                      (generate-temporaries #'[method-id ...]))

   ; Now that we’ve expanded the types above for the purpose of inclusion in the class’s method table,
   ; we want to reexpand the type with the proper quantifier and constraint, since uses of the method
   ; should actually see that type.
   #:with [quantified-t:type ...]
          #'[(∀ [var-id ...] (=> [(@%app (#%type:con name) var-id ...)] bare-t)) ...]

   (~> (quasitemplate
        (begin-
          (define-values [] method-t.residual) ...
          (define-values [] super-constr.residual) ...
          (define- (method-id- dict) (free-id-table-ref- dict #'method-id)) ...
          #,@(for/list ([method-id (in-list (attribute method-id))]
                        [method-id- (in-list (attribute method-id-))]
                        [fixity (in-list (attribute fixity.fixity))]
                        [quantified-t (in-list (attribute quantified-t.expansion))])
               (indirect-infix-definition
                #`(define-syntax- #,method-id
                    (make-typed-var-transformer #'#,method-id- (quote-syntax #,quantified-t)))
                fixity))
          {?? (def method-default-id- : quantified-t #:exact method-default-impl)} ...
          (define-syntax- name
            (make-class:info (list #'var-id- ...)
                             (make-immutable-free-id-table
                              (list (cons #'method-id (quote-syntax method-t.expansion)) ...))
                             (make-immutable-free-id-table
                              (list {?? (cons #'method-id #'method-default-id-)} ...))
                             (list (quote-syntax super-constr.expansion) ...)
                             (set (functional-dependency
                                   (immutable-free-id-set (list (quote-syntax fundep-lhs-) ...))
                                   (immutable-free-id-set (list (quote-syntax fundep-rhs-) ...)))
                                  ...)
                             deriving-transformer))))
       (syntax-property 'disappeared-binding (map syntax-local-introduce (attribute var-id-)))
       (syntax-property 'disappeared-use
                        (map syntax-local-introduce
                             (filter values (cons (attribute =>/use)
                                                  (append (attribute :/use)
                                                          (attribute ->/use)
                                                          (append* (attribute fundep-lhs-))
                                                          (append* (attribute fundep-rhs-))))))))])

(begin-for-syntax
  (define-syntax-class instance-head
    #:description "instance head"
    #:attributes [class class.local-value [bare-t 1]]
    [pattern {~type (class:class-id bare-t ...)}])

  (define-syntax-class instance-spec
    #:description "instance spec"
    #:attributes [[var-id 1] [constr 1] ∀/use =>/use class class.local-value [bare-t 1] head-stx]
    #:literals [∀ =>]
    #:commit
    [pattern {~post {~and :instance-head head-stx}}
             #:attr ∀/use #f
             #:attr =>/use #f
             #:attr [var-id 1] '()
             #:attr [constr 1] '()]
    [pattern ({~type ∀/use:∀} ~!
              [{~type var-id:id} ...]
              {~optional {~seq {~type constr} ... {~type =>/use:=>}}
                         #:defaults ([[constr 1] '()])}
              ~! {~and :instance-head head-stx})]
    [pattern (constr ... {~type =>/use:=>} ~! {~and :instance-head head-stx})
             #:attr ∀/use #f
             #:attr [var-id 1] '()]))

(define-syntax-parser instance
  #:literals [∀ =>]
  [(_ :instance-spec [method-id:id impl:expr] ...)
   ; Validate that the number of types in the instance head is the same as the number of parameters of
   ; the class being implemented.
   #:do [(define class-info (attribute class.local-value))]
   #:fail-when (and (not (= (length (class:info-vars class-info)) (length (attribute bare-t))))
                    #'head-stx)
               (~a "wrong number of parameters for class ‘" (syntax-e #'class) "’; expected "
                   (length (class:info-vars class-info)) ", given " (length (attribute bare-t)))

   ; Expand each provided subgoal and type in the instance head in a context where the various type
   ; variables are bound.
   #:do [(define t-intdef-ctx (syntax-local-make-definition-context))]
   #:with [var-id- ...] (map #{internal-definition-context-introduce t-intdef-ctx %}
                             (attribute var-id))
   #:do [(syntax-local-bind-syntaxes (attribute var-id) #f t-intdef-ctx)]
   #:with [(~var constr- (type t-intdef-ctx)) ...] (attribute constr)
   #:with [(~var bare-t- (type t-intdef-ctx)) ...] (attribute bare-t)

   ; Reduce the instance context, and include the instance currently being defined as a tautological
   ; constraint to eliminate silly things like (instance (forall [a] (Eq (X a)) => (Eq (X a))) ....).
   #:with (~var this-instance-constr (type t-intdef-ctx)) #'(@%app class bare-t-.expansion ...)
   #:with [constr-/reduced ...] (reduce-context
                                 (attribute constr-.expansion)
                                 #:extra-tautological-constrs (list #'this-instance-constr.expansion))

   ; Check that the instance is not overlapping.
   #:do [(define overlapping-instances
           (lookup-overlapping-instances class-info (attribute bare-t-.expansion)))]
   #:fail-unless (empty? overlapping-instances)
                 (let ([s? (if (> (length overlapping-instances) 1) "s" "")])
                   (~a "instance overlaps with previously-declared instance" s? "\n"
                       "  instance" s? ":\n    "
                       (string-join (map class:instance->string overlapping-instances)
                                    "\n    ")))
   
   ; Ensure all the provided methods belong to the class being implemented and ensure that none of the
   ; non-optional methods are unimplemented.
   #:do [(define method-table (class:info-method-table class-info))
         (define default-methods (class:info-default-methods class-info))
         
         (define all-method-ids (free-id-table-keys method-table))
         (define optional-method-ids (free-id-table-keys default-methods))
         (define required-method-ids (remove* optional-method-ids all-method-ids free-identifier=?))

         (define invalid-methods (filter-not #{member % all-method-ids free-identifier=?}
                                             (attribute method-id)))
         (define missing-methods (filter-not #{member % (attribute method-id) free-identifier=?}
                                             required-method-ids))]
   #:fail-when (and (not (empty? invalid-methods)) (first invalid-methods))
               (~a "not a method of class ‘" (syntax-e #'class) "’")
   #:fail-when (and (not (empty? missing-methods)) #'class)
               (~a "missing implementation of ‘" (syntax-e (first missing-methods)) "’")

   ; With the types actually expanded, we need to skolemize them for the pupose of typechecking
   ; method implementations.
   #:do [(define skolem-ids (generate-temporaries (attribute var-id)))
         (define var+skolem-ids
           (map #{cons %1 #`(#%type:rigid-var #,%2)} (attribute var-id-) skolem-ids))
         (define bare-ts/skolemized (map #{insts % var+skolem-ids} (attribute bare-t-.expansion)))]
   #:with [constr/skolemized ...] (map #{insts % var+skolem-ids} (attribute constr-/reduced))

   ; With the skolemized constraints and instance head, we need to synthesize expected types for each
   ; typeclass method by replacing each variable in the class signatures with the corresponding type
   ; from the instance head.
   #:with [expected-t ...]
          (let* ([class-vars (class:info-vars class-info)]
                 [class-vars->bare-ts-subst (map cons class-vars bare-ts/skolemized)])
            (for/list ([method-id (in-list all-method-ids)])
              (insts (free-id-table-ref method-table method-id) class-vars->bare-ts-subst)))

   ; Now we need to align user-provided method implementations with their types, substituting in the
   ; default implementation whenever an explicit implementation is not provided.
   #:with [every-method-id ...] all-method-ids
   #:do [(define provided-impls (make-immutable-free-id-table
                                 (map cons (attribute method-id) (attribute impl))))]
   #:with [every-impl ...] (for/list ([method-id (in-list all-method-ids)])
                             (let ([provided-impl (free-id-table-ref provided-impls method-id #f)])
                               (or provided-impl (free-id-table-ref default-methods method-id))))

   ; Finally, generate some temporaries and expressions needed in the output.
   #:with dict-id- (generate-temporary #'class)
   #:with [superclass-constr ...]
          (let ([insts-map (map cons (class:info-vars class-info) bare-ts/skolemized)])
            (for/list ([constr (in-list (class:info-superclasses class-info))])
              (insts constr insts-map)))

   (~> #`(begin-
           (define-values [] constr-.residual) ...
           (define-values [] bare-t-.residual) ...
           (begin-for-syntax-
             (register-global-class-instance!
              (class:instance (quote-syntax class)
                              (list (quote-syntax var-id-) ...)
                              (list (quote-syntax constr-/reduced) ...)
                              (list (quote-syntax bare-t-.expansion) ...)
                              (quote-syntax dict-id-))))
           ; The defined dict-id- might appear in the expansion of :/instance-dictionary, since it
           ; performs dictionary elaboration. At the top level, this can cause problems, since
           ; recursive/self-referential definitions are complicated. We can perform a sort of “forward
           ; declaration” by using a special case of define-syntaxes (that only works at the top
           ; level) to declare identifiers without binding them; see the documentation for
           ; define-syntaxes for details.
           #,(if (eq? 'top-level (syntax-local-context))
                 #'(define-syntaxes- [dict-id-] (values))
                 #'(begin-))
           (define- dict-id-
             #,(syntax/loc this-syntax
                 (:/instance-dictionary
                  #:methods ([every-method-id : expected-t every-impl] ...)
                  #:instance-constrs [constr/skolemized ...]
                  #:superclass-constrs [superclass-constr ...]))))
       (syntax-property 'disappeared-binding
                        (~>> (attribute var-id)
                             (map (λ~>> (internal-definition-context-introduce t-intdef-ctx)
                                        syntax-local-introduce))))
       (syntax-property 'disappeared-use
                        (~>> (map syntax-local-introduce (attribute method-id))
                             (cons (syntax-local-introduce #'class))
                             (cons (and~> (attribute ∀/use) syntax-local-introduce))
                             (cons (and~> (attribute =>/use) syntax-local-introduce)))))])

(define-syntax-parser :/instance-dictionary
  #:literals [:]
  [(_ #:methods ([method-id : method-t method-impl] ...)
      #:instance-constrs [instance-constr-expr ...]
      #:superclass-constrs [superclass-constr-expr ...])

   #:with [superclass-dict-placeholder ...]
          (for/list ([constr-expr (in-list (attribute superclass-constr-expr))])
            (quasisyntax/loc this-syntax
              (@%dictionary-placeholder #,constr-expr #,this-syntax)))

   (~> #'(make-immutable-free-id-table-
          (list- (cons- (quote-syntax @%superclasses-key)
                        (vector-immutable- superclass-dict-placeholder ...))
                 (cons- (quote-syntax method-id) (: method-impl method-t #:exact)) ...))
       ; Wrap the entire expression with lambdas for the appropriate subgoal dictionaries
       (foldl #{begin #`(@%with-dictionary #,%1 #,%2)} _ (attribute instance-constr-expr)))])

(define-syntax-parser derive-instance
  [(_ {~type {~var class (class-id #:require-deriving-transformer? #t)}} . _)
   #:with result ((class:info-deriving-transformer (attribute class.local-value)) this-syntax)
   (syntax-property #'result 'disappeared-use
                    (cons (syntax-local-introduce #'class)
                          (syntax-property #'result 'disappeared-use)))])
