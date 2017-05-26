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
         (only-in hackett/private/kernel ∀ => [#%app @%app]))

(provide (for-syntax class-id)
         class instance)

(begin-for-syntax
  (define-syntax-class/specialize class-id
    (local-value class:info? #:failure-message "identifier was not bound to a class")))

(define-syntax-parser class
  #:literals [: => let-values #%plain-app]
  [(_ {~optional {~seq constr ... =>/use:=>}}
      (name:id var-id:id)
      [method-id:id
       {~or {~once {~seq : bare-t}}
            {~optional fixity:fixity-annotation}}
       ...]
      ...)
   ; The methods in a class’s method table should *not* be quantified. That is, in this class:
   ;
   ;    (class (Show a)
   ;      [show : (-> a a)])
   ;
   ; The type for show stored in the method table should be (-> a a), not
   ; (∀ [a] (=> [(Show a)] (-> a a))). However, in order to expand the user-provided (-> a a) type in
   ; a context where ‘a’ is bound, we need to bind it with let-syntax and manually call local-expand.
   ; We also want to do the same thing with superclass constraints so that the same variable is bound
   ; in both situations.
   #:with var-id- (generate-temporary #'var-id)
   #:with var-id-expr (preservable-property->expression (τ:var #'var-id-))
   #:with (let-values () {~and inner-let (let-values ()
                                           [#%plain-app _ method-t:type ...]
                                           [#%plain-app _ super-constr:type ...])})
          (local-expand-type (template
                              (let-syntax- ([var-id (make-type-variable-transformer var-id-expr)])
                                (void- bare-t ...)
                                (void- {?? {?@ constr ...}}))))
   #:with [method-id- ...] (generate-temporaries #'[method-id ...])
   #:with [method-t-expr ...] (map preservable-property->expression (attribute method-t.τ))
   #:with [super-constr-expr ...] (map preservable-property->expression
                                       (attribute super-constr.τ))

   ; Now that we’ve manually expanded the types above for the purpose of inclusion in the class’s
   ; method table, we want to reexpand the type with the proper quantifier and constraint, since uses
   ; of the method should actually see that type.
   #:with name-t (τ-stx-token (τ:con #'name #f))
   #:with [quantified-t:type ...] #'[(∀ [var-id] (=> [(@%app name-t var-id)] bare-t)) ...]
   #:with [quantified-t-expr ...] (map preservable-property->expression (attribute quantified-t.τ))

   #`(begin-
       (define-values- []
         #,(~> #'(begin- (λ- () method-t.expansion) ...
                         (λ- () super-constr.expansion) ...
                         (values-))
               (syntax-property 'disappeared-binding
                                (syntax-property #'inner-let 'disappeared-binding))))
       (define- (method-id- dict) (free-id-table-ref- dict #'method-id)) ...
       #,@(for/list ([method-id (in-list (attribute method-id))]
                     [method-id- (in-list (attribute method-id-))]
                     [fixity (in-list (attribute fixity.fixity))]
                     [quantified-t-expr (in-list (attribute quantified-t-expr))])
            (indirect-infix-definition
             #`(define-syntax- #,method-id
                 (make-typed-var-transformer #'#,method-id- #,quantified-t-expr))
             fixity))
       (define-syntax- name
         (class:info #'var-id-
                     (make-immutable-free-id-table
                      (list (cons #'method-id method-t-expr) ...))
                     (list super-constr-expr ...))))])

(define-syntax-parser instance
  #:literals [∀ =>]
  [(_ {~optional {~seq ∀/use:∀ [var-id:id ...]} #:defaults ([[var-id 1] '()])}
      {~optional {~seq constr ... =>/use:=>} #:defaults ([[constr 1] '()])}
      (class:class-id bare-t)
      [method-id:id impl:expr] ...)

   ; Ensure all the provided methods belong to the class being implemented and ensure that none of the
   ; methods are unimplemented.
   #:do [(define class-info (attribute class.local-value))
         (define method-table (class:info-method-table class-info))
         (define expected-methods (free-id-table-keys method-table))
         (define invalid-methods (filter-not #{member % expected-methods free-identifier=?}
                                             (attribute method-id)))
         (define missing-methods (filter-not #{member % (attribute method-id) free-identifier=?}
                                             expected-methods))]
   #:fail-when (and (not (empty? invalid-methods)) (first invalid-methods))
               (~a "not a method of class ‘" (syntax-e #'class) "’")
   #:fail-when (and (not (empty? missing-methods)) #'class)
               (~a "missing implementation of ‘" (syntax-e (first missing-methods)) "’")

   ; Calculate the expected type of each method. First, we have to expand the provided type in a
   ; context where the various type variables are bound. We then need to extract the expanded base
   ; type and separate its variables so that we can instantiate the type of individual class methods,
   ; then quantify over the whole thing.
   #:with t:type (let ([constrained (if (empty? (attribute constr))
                                        #'bare-t
                                        #'(=>/use [constr ...] bare-t))])
                   (if (empty? (attribute var-id))
                       constrained
                       #`(∀/use [var-id ...] #,constrained)))
   #:do [(define skolem-vars (generate-temporaries (attribute var-id)))
         (modify-type-context #{append % (map ctx:skolem skolem-vars)})
         (define-values [constrs- bare-t-]
           (let skolemize-loop ([skolems-left skolem-vars]
                                [bare-t- (attribute t.τ)])
             (if (empty? skolems-left)
                 (let collect-constraints-loop ([constrs- '()]
                                                [bare-t- bare-t-])
                   (if (< (length constrs-) (length (attribute constr)))
                       (match-let ([(τ:qual constr t) bare-t-])
                         (collect-constraints-loop (cons constr constrs-) t))
                       (values constrs- bare-t-)))
                 (match-let ([(τ:∀ id t) bare-t-])
                   (skolemize-loop (rest skolems-left)
                                   (inst t id (τ:skolem (first skolems-left))))))))]
   #:do [(define expected-ts
           (let ([x (class:info-var class-info)])
             (for/list ([method-id (in-list (attribute method-id))])
               (let ([t (free-id-table-ref method-table method-id)])
                 (inst t x bare-t-)))))]

   #:with t-expr (preservable-property->expression (attribute t.τ))

   ; Generate some temporaries and expressions needed in the output.
   #:with dict-id- (generate-temporary #'class)
   #:with [expected-t-expr ...] (map preservable-property->expression expected-ts)
   #:with [constr-expr ...] (map preservable-property->expression constrs-)
   #:with [superclass-constr-expr ...] (map (λ~> (inst (class:info-var class-info) bare-t-)
                                                 preservable-property->expression)
                                            (class:info-superclasses class-info))

   (~> #`(begin-
           (begin-for-syntax-
             (register-global-class-instance!
              (class:instance (syntax-local-value #'class)
                              t-expr
                              #'dict-id-)))
           (define-values- [] (begin- (λ- () t.expansion) (values-)))
           (define- dict-id-
             #,(syntax/loc this-syntax
                 (:/instance-dictionary
                  #:methods ([method-id : expected-t-expr impl] ...)
                  #:instance-constrs [constr-expr ...]
                  #:superclass-constrs [superclass-constr-expr ...]))))
       (syntax-property 'disappeared-use
                        (~>> (map syntax-local-introduce (attribute method-id))
                             (cons (syntax-local-introduce #'class)))))])

(define-syntax-parser :/instance-dictionary
  #:literals [:]
  [(_ #:methods ([method-id : method-t-expr method-impl] ...)
      #:instance-constrs [instance-constr-expr ...]
      #:superclass-constrs [superclass-constr-expr ...])

   #:with [method-t ...] (generate-temporaries (attribute method-t-expr))
   #:with [superclass-dict-placeholder ...]
          (for/list ([constr-expr (in-list (attribute superclass-constr-expr))])
            (quasisyntax/loc this-syntax
              (@%dictionary-placeholder #,constr-expr)))

   (~> #'(let-syntax- ([method-t (make-type-variable-transformer method-t-expr)] ...)
           (make-immutable-free-id-table-
            (list- (cons- (quote-syntax @%superclasses-key)
                          (vector-immutable- superclass-dict-placeholder ...))
                   (cons- (quote-syntax method-id) (: method-impl method-t)) ...)))
       ; Wrap the entire expression with lambdas for the appropriate subgoal dictionaries
       (foldr #{begin #`(@%with-dictionary #,%1 #,%2)} _ (attribute instance-constr-expr))
       ; Perform dictionary elaboration on the whole expression
       (local-expand 'expression '())
       elaborate-dictionaries)])
