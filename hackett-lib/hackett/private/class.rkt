#lang curly-fn racket/base

(require racket/require hackett/private/util/require)

(require (for-syntax (multi-in racket [base format list match syntax])
                     (multi-in syntax/parse [class/local-value experimental/specialize
                                             experimental/template])
                     syntax/id-table
                     threading)
         (postfix-in - (combine-in racket/base
                                   syntax/id-table))
         syntax/parse/define

         (for-syntax hackett/private/infix
                     hackett/private/util/stx)
         (except-in hackett/private/base ∀ => @%app)
         (only-in hackett/private/kernel
                  [#%hackett-type:∀ ∀]
                  [#%hackett-type:=> =>]
                  [#%app @%app]))

(provide (for-syntax class-id)
         class instance)

(begin-for-syntax
  (define-syntax-class/specialize class-id
    (local-value class:info? #:failure-message "identifier was not bound to a class")))

(define-syntax-parser class
  #:literals [: => let-values #%plain-app]
  [(_ {~optional {~seq {~type constr} ... {~type =>/use:=>}} #:defaults ([[constr 1] '()])}
      {~type (name:id var-id:id ...)}
      [method-id:id
       {~or {~once {~seq {~and : {~var :/use}} {~type bare-t}}}
            {~optional fixity:fixity-annotation}}
       ...
       {~optional method-default-impl:expr}]
      ...)
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
   #:with [var-id- ...] (generate-temporaries (attribute var-id))
   #:do [(define t-intdef-ctx (syntax-local-make-definition-context))]
   #:with [var-id-* ...] (map #{internal-definition-context-introduce t-intdef-ctx %}
                              (attribute var-id-))
   #:do [(syntax-local-bind-syntaxes (attribute var-id-) #f t-intdef-ctx)
         (syntax-local-bind-syntaxes
          (attribute var-id)
          #'(values (make-type-variable-transformer (τ:var (quote-syntax var-id-*))) ...)
          t-intdef-ctx)]

   #:with [(~var method-t (type t-intdef-ctx)) ...] (attribute bare-t)
   #:with [(~var super-constr (type t-intdef-ctx)) ...] (attribute constr)
   
   #:with [method-id- ...] (generate-temporaries #'[method-id ...])
   #:with [method-default-id- ...] (generate-temporaries #'[method-id ...])
   #:with [method-t-expr ...] (map preservable-property->expression (attribute method-t.τ))
   #:with [super-constr-expr ...] (map preservable-property->expression
                                       (attribute super-constr.τ))

   ; Now that we’ve expanded the types above for the purpose of inclusion in the class’s method table,
   ; we want to reexpand the type with the proper quantifier and constraint, since uses of the method
   ; should actually see that type.
   #:with name-t (τ-stx-token (τ:con #'name #f))
   #:with [quantified-t:type ...] #'[(∀ [var-id ...] (=> [(@%app name-t var-id ...)] bare-t)) ...]
   #:with [quantified-t-expr ...] (map preservable-property->expression (attribute quantified-t.τ))

   ; This use of syntax-local-introduce is necessary due to how local-expand and
   ; syntax-local-bind-syntaxes implicitly call syntax-local-introduce, and how types store syntax in
   ; syntax properties. For more details, see the comment above the corresponding definition in the
   ; ‘instance’ form.
   #:with [var-id-** ...] (map syntax-local-introduce (attribute var-id-*))

   (~> (quasitemplate
        (begin-
          (define-values- []
            (begin- (λ- () method-t.expansion) ...
                    (λ- () super-constr.expansion) ...
                    (values-)))
          (define- (method-id- dict) (free-id-table-ref- dict #'method-id)) ...
          #,@(for/list ([method-id (in-list (attribute method-id))]
                        [method-id- (in-list (attribute method-id-))]
                        [fixity (in-list (attribute fixity.fixity))]
                        [quantified-t-expr (in-list (attribute quantified-t-expr))])
               (indirect-infix-definition
                #`(define-syntax- #,method-id
                    (make-typed-var-transformer #'#,method-id- #,quantified-t-expr))
                fixity))
          {?? (def method-default-id- : quantified-t method-default-impl)} ...
          (define-syntax- name
            (class:info (list #'var-id-** ...)
                        (make-immutable-free-id-table
                         (list (cons #'method-id method-t-expr) ...))
                        (make-immutable-free-id-table
                         (list {?? (cons #'method-id #'method-default-id-)} ...))
                        (list super-constr-expr ...)))))
       (syntax-property 'disappeared-binding
                        (~>> (attribute var-id)
                             (map (λ~>> (internal-definition-context-introduce t-intdef-ctx)
                                        syntax-local-introduce))))
       (syntax-property 'disappeared-use (map syntax-local-introduce (attribute :/use))))])

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
    [pattern (constr ... {~type =>/use:=>} {~and :instance-head head-stx})
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
   
   ; Ensure all the provided methods belong to the class being implemented and ensure that none of the
   ; non-optional methods are unimplemented.
   #:do [(define class-info (attribute class.local-value))
         (define method-table (class:info-method-table class-info))
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

   ; Calculate the expected type of each method. First, we have to expand each provided subgoal and
   ; type in the instance head in a context where the various type variables are bound.
   #:with [var-id- ...] (generate-temporaries (attribute var-id))
   #:do [(define t-intdef-ctx (syntax-local-make-definition-context))]
   #:with [var-id-* ...] (map #{internal-definition-context-introduce t-intdef-ctx %}
                              (attribute var-id-))
   #:do [(syntax-local-bind-syntaxes (attribute var-id-) #f t-intdef-ctx)
         (syntax-local-bind-syntaxes
          (attribute var-id)
          #`(values (make-type-variable-transformer (τ:var (quote-syntax var-id-*))) ...)
          t-intdef-ctx)]
   #:with [(~var constr- (type t-intdef-ctx)) ...] (attribute constr)
   #:with [(~var bare-t- (type t-intdef-ctx)) ...] (attribute bare-t)

   ; With the types actually expanded, we need to skolemize them for the pupose of typechecking
   ; method implementations.
   ;
   ; This extra syntax-local-introduce on var-id-* is necessary because local-expand and
   ; syntax-local-bind-syntaxes implicitly call syntax-local-introduce (because they implicitly switch
   ; to “macro result view”, according to mflatt). Normally, this wouldn’t be a problem, since
   ; local-expand also calls syntax-local-introduce again on its *result*, flipping the scopes back.
   ; However, types are placed in syntax properties, and syntax properties are not adjusted by the
   ; expander. This means the use-site and macro-introduction scopes are still in the
   ; “macro result view”, and they won’t be free-identifier=? to the var-id-* we have a reference to
   ; unless we explicitly call syntax-local-introduce.
   #:with [var-id-** ...] (map syntax-local-introduce (attribute var-id-*))
   #:do [(define skolem-ids (generate-temporaries (attribute var-id)))
         (modify-type-context #{append % (map ctx:skolem skolem-ids)})
         (define var+skolem-ids (map #{cons %1 (τ:skolem %2)} (attribute var-id-**) skolem-ids))
         (define constrs/skolemized (map #{insts % var+skolem-ids} (attribute constr-.τ)))
         (define bare-ts/skolemized (map #{insts % var+skolem-ids} (attribute bare-t-.τ)))]

   ; With the skolemized constraints and instance head, we need to synthesize expected types for each
   ; typeclass method by replacing each variable in the class signatures with the corresponding type
   ; from the instance head.
   #:do [(define expected-ts
           (let* ([class-vars (class:info-vars class-info)]
                  [class-vars->bare-ts-subst (map cons class-vars bare-ts/skolemized)])
             (for/list ([method-id (in-list all-method-ids)])
               (insts (free-id-table-ref method-table method-id) class-vars->bare-ts-subst))))]

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
   #:with [expected-t-expr ...] (map preservable-property->expression expected-ts)
   #:with [bare-t-expr ...] (map preservable-property->expression (attribute bare-t-.τ))
   #:with [constr-expr ...] (map preservable-property->expression (attribute constr-.τ))
   #:with [constr/skolemized-expr ...] (map preservable-property->expression constrs/skolemized)
   #:with [superclass-constr-expr ...]
          (map (λ~> (insts (map cons (class:info-vars class-info) bare-ts/skolemized))
                    preservable-property->expression)
               (class:info-superclasses class-info))

   (~> #`(begin-
           (begin-for-syntax-
             (register-global-class-instance!
              (class:instance (syntax-local-value #'class)
                              (list (quote-syntax var-id-**) ...)
                              (list constr-expr ...)
                              (list bare-t-expr ...)
                              #'dict-id-)))
           (define-values- [] (begin- (λ- () constr-.expansion) ...
                                      (λ- () bare-t-.expansion) ...
                                      (values-)))
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
                  #:methods ([every-method-id : expected-t-expr every-impl] ...)
                  #:instance-constrs [constr/skolemized-expr ...]
                  #:superclass-constrs [superclass-constr-expr ...]))))
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
  [(_ #:methods ([method-id : method-t-expr method-impl] ...)
      #:instance-constrs [instance-constr-expr ...]
      #:superclass-constrs [superclass-constr-expr ...])

   #:with [method-t ...] (generate-temporaries (attribute method-t-expr))
   #:with [superclass-dict-placeholder ...]
          (for/list ([constr-expr (in-list (attribute superclass-constr-expr))])
            (quasisyntax/loc this-syntax
              (@%dictionary-placeholder #,constr-expr #,this-syntax)))

   (~> #'(let-syntax- ([method-t (make-type-variable-transformer method-t-expr)] ...)
           (make-immutable-free-id-table-
            (list- (cons- (quote-syntax @%superclasses-key)
                          (vector-immutable- superclass-dict-placeholder ...))
                   (cons- (quote-syntax method-id) (: method-impl method-t)) ...)))
       ; Wrap the entire expression with lambdas for the appropriate subgoal dictionaries
       (foldl #{begin #`(@%with-dictionary #,%1 #,%2)} _ (attribute instance-constr-expr)))])
