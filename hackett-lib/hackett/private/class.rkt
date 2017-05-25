#lang curly-fn racket/base

(require racket/require hackett/private/util/require)

(require (for-syntax (multi-in racket [base format list match syntax])
                     (multi-in syntax/parse [class/local-value experimental/specialize])
                     syntax/id-table
                     threading)
         (postfix-in - (combine-in racket/base
                                   syntax/id-table))
         syntax/parse/define

         (for-syntax hackett/private/infix
                     hackett/private/util/stx)
         (except-in hackett/private/base ∀ =>)
         (only-in hackett/private/kernel ∀ =>))

(provide (for-syntax class-id)
         class instance)

(begin-for-syntax
  (define-syntax-class/specialize class-id
    (local-value class:info? #:failure-message "identifier was not bound to a class")))

(define-syntax-parser class
  #:literals [: let-values]
  [(_ (name:id var-id:id)
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
   #:with var-id- (generate-temporary #'var-id)
   #:with var-id-expr (preservable-property->expression (τ:var #'var-id-))
   #:with (let-values () (let-values () method-t:type ... _))
          (local-expand-type #'(let-syntax ([var-id (make-type-variable-transformer var-id-expr)])
                                 bare-t ... (void)))
   #:with [method-id- ...] (generate-temporaries #'[method-id ...])
   #:with [method-id/prefix ...] (generate-temporaries #'[method-id ...])
   #:with [method-t-expr ...] (map preservable-property->expression (attribute method-t.τ))

   ; Now that we’ve manually expanded the types above for the purpose of inclusion in the class’s
   ; method table, we want to reexpand the type with the proper quantifier and constraint, since uses
   ; of the method should actually see that type.
   #:with [quantified-t:type ...] #'[(∀ [var-id] (=> [(name var-id)] bare-t)) ...]
   #:with [quantified-t-expr ...] (map preservable-property->expression (attribute quantified-t.τ))

   #`(begin-
       (define-values- [] (begin- (λ- () quantified-t.expansion) ... (values-)))
       (define- (method-id- dict) (free-id-table-ref- dict #'method-id)) ...
       #,@(for/list ([method-id (in-list (attribute method-id))]
                     [method-id- (in-list (attribute method-id-))]
                     [method-id/prefix (in-list (attribute method-id/prefix))]
                     [fixity (in-list (attribute fixity.fixity))]
                     [quantified-t-expr (in-list (attribute quantified-t-expr))])
            (indirect-infix-definition
             #`(define-syntax- #,method-id
                 (make-typed-var-transformer #'#,method-id- #,quantified-t-expr))
             fixity))
       (define-syntax- name
         (class:info #'var-id- (make-immutable-free-id-table
                                (list (cons #'method-id method-t-expr) ...)))))])

(define-syntax-parser instance
  #:literals [∀ =>]
  [(_ {~optional {~seq ∀/use:∀ [var-id:id ...]} #:defaults ([[var-id 1] '()])}
      {~optional {~seq [constr ...] =>/use:=>} #:defaults ([[constr 1] '()])}
      (class:class-id bare-t)
      [method-id:id impl:expr] ...)

   ; Ensure all the provided methods belong to the class being implemented and ensure that none of the
   ; methods are unimplemented.
   #:do [(define method-table (class:info-method-table (attribute class.local-value)))
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
           (let ([x (class:info-var (attribute class.local-value))])
             (for/list ([method-id (in-list (attribute method-id))])
               (let ([t (free-id-table-ref method-table method-id)])
                 (inst t x bare-t-)))))]

   #:with t-expr (preservable-property->expression (attribute t.τ))

   ; Generate some temporaries for the necessary runtime bindings.
   #:with [impl-id- ...] (generate-temporaries #'[impl ...])
   #:with [subdict-id- ...] (generate-temporaries #'[constr ...])
   #:with [impl-fn-spec- ...] (if (empty? (attribute constr))
                                  (attribute impl-id-)
                                  (map #{begin #`(#,% subdict-id- ...)} (attribute impl-id-)))
   #:with dict-id- (generate-temporary #'class)
   #:with dict-fn-spec- (foldl #{begin #`(#,%2 #,%1)} #'dict-id- (attribute subdict-id-))
   #:with [expected-t-expr ...] (map preservable-property->expression expected-ts)
   #:with [constr-expr ...] (map preservable-property->expression constrs-)

   (~> #'(begin-
           (begin-for-syntax-
             (register-global-class-instance!
              (class:instance (syntax-local-value #'class)
                              t-expr
                              #'dict-id-)))
           (define-values- [] (begin- (λ- () t.expansion) (values-)))
           (define- impl-fn-spec-
             (:/class-method impl expected-t-expr
                             #:constraints [constr-expr ...]
                             #:subdict-ids [subdict-id- ...]))
           ...
           (define- dict-fn-spec-
             (make-immutable-free-id-table-
              (list- (cons- #'method-id impl-fn-spec-) ...))))
       (syntax-property 'disappeared-use
                        (~>> (map syntax-local-introduce (attribute method-id))
                             (cons (syntax-local-introduce #'class)))))])

(define-syntax-parser :/class-method
  [(_ e-expr:expr t-expr:expr
      #:constraints [constraint-expr:expr ...]
      #:subdict-ids [subdict-id-expr:id ...])
   #'(let-syntax
         ([result
           (let ([e #'e-expr]
                 [t t-expr]
                 [constraints (list constraint-expr ...)]
                 [subdict-ids (list #'subdict-id-expr ...)])
             (let ([subgoal-instances
                    (for/list ([constr (in-list constraints)]
                               [subdict-id (in-list subdict-ids)])
                      (match-let ([(constr:class class-id t) constr])
                        (class:instance (syntax-local-value class-id) t subdict-id)))])
               (make-variable-like-transformer
                (parameterize ([local-class-instances
                                (append subgoal-instances (local-class-instances))])
                  (local-expand (elaborate-dictionaries (local-expand (τ⇐! e t) 'expression '()))
                                'expression '())))))])
       result)])
