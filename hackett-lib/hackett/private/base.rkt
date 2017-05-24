#lang curly-fn racket/base

(require racket/require hackett/private/util/require)

(require (for-syntax (multi-in racket [base contract list match syntax])
                     syntax/id-table
                     syntax/parse
                     threading)
         (postfix-in - (combine-in racket/base
                                   racket/promise
                                   syntax/id-table))
         (multi-in racket [match splicing])
         syntax/parse/define

         (for-syntax hackett/private/infix
                     hackett/private/typecheck
                     hackett/private/util/list
                     hackett/private/util/stx))

(provide (for-syntax (all-from-out hackett/private/typecheck)
                     τ⇐/λ! τ⇐! τ⇒/λ! τ⇒! τ⇒app! τs⇒! elaborate-dictionaries)
         #%module-begin #%top
         (rename-out [#%module-begin @%module-begin]
                     [#%top @%top]
                     [∀ forall])
         @%datum @%app @%top-interaction
         define-primop define-base-type
         -> ∀ => Integer String
         : :/top-level with-dictionary-elaboration λ1 def)

(define-simple-macro (define-base-type name:id)
  (define-syntax name (make-type-variable-transformer (τ:con #'name #f))))

(define-base-type Integer)
(define-base-type String)

(define-syntax-parser define-primop
  [(_ op:id op-:id t-expr:type)
   #:with t (preservable-property->expression (attribute t-expr.τ))
   #'(define-syntax op (make-typed-var-transformer #'op- t))])

(define-syntax ->/prefix (make-type-variable-transformer τ:->))
(define-syntax -> (infix-operator-impl #'->/prefix 'right))

(define-syntax-parser ∀
  #:literals [let-values]
  [(_ x:id t)
   #:with x- (generate-temporary #'x)
   #:with x/τ (preservable-property->expression (τ:var #'x-))
   #:with (let-values _ (let-values _ t-:type))
          (local-expand-type #'(let-syntax ([x (make-variable-like-transformer
                                                (τ-stx-token x/τ))])
                                 t))
   (τ-stx-token (τ:∀ #'x- (attribute t-.τ)))])
(define-syntax-parser =>
  [(_ (class-id:id t:type) a:type)
   (τ-stx-token (τ:qual (constr:class #'class-id (attribute t.τ)) (attribute a.τ)))])

(define (@%dictionary-placeholder . args)
  (error '@%dictionary-placeholder "should never appear at runtime"))

(define (@%with-dictionary . args)
  (error '@%with-dictionary "should never appear at runtime"))

(begin-for-syntax
  (define/contract (τ⇒/λ! e bindings)
    (-> syntax? (listof (cons/c identifier? τ?)) (values (listof identifier?) syntax? τ?))
    (define/syntax-parse [x ...] (map car bindings))
    (define/syntax-parse [x- ...] (generate-temporaries (attribute x)))
    (define/syntax-parse [t_x ...] (map (λ~> cdr preservable-property->expression) bindings))
    (define-values [xs- e-]
      (syntax-parse (local-expand #`(λ (x- ...)
                                      (let-syntax ([x (make-typed-var-transformer #'x- t_x)] ...)
                                        #,e))
                                  'expression '())
        #:literals [#%plain-lambda let-values]
        [(#%plain-lambda (x-* ...) (let-values _ (let-values _ e-)))
         (values (attribute x-*) #'e-)]))
    (define t_e (get-type e-))
    (unless t_e (raise-syntax-error #f "no inferred type" e))
    (values xs- e- t_e))

  (define/contract (τ⇐/λ! e t bindings)
    (-> syntax? τ? (listof (cons/c identifier? τ?)) (values (listof identifier?) syntax?))
    (current-τ-wf! t)
    (match t
      [(τ:∀ x a)
       (let ([x^ (generate-temporary x)])
         (modify-type-context #{snoc % (ctx:skolem x^)})
         (begin0
           (τ⇐/λ! e (inst a x (τ:skolem x^)) bindings)
           (modify-type-context #{ctx-remove % (ctx:skolem x^)})))]
      [(τ:qual constr a)
       (let*-values ([(xs- e-) (τ⇐/λ! e a bindings)])
         (values xs- (quasisyntax/loc e-
                       (@%with-dictionary #,(preservable-property->expression constr) #,e-))))]
      [_
       (define-values [xs- e- t_e] (τ⇒/λ! (attach-expected e t) bindings))
       (define constrs (τ<:/elaborate! t_e t #:src e))
       (values xs- (foldr #{begin (quasisyntax/loc e
                                    (lazy- (#%app- (force- #,%2)
                                                   #,(quasisyntax/loc e
                                                       (@%dictionary-placeholder
                                                        #,(preservable-property->expression %1))))))}
                          e- constrs))]))

  (define/contract (τ⇒! e)
    (-> syntax? (values syntax? τ?))
    (match-let-values ([(_ e- t_e) (τ⇒/λ! e '())])
      (values e- t_e)))

  (define/contract (τ⇐! e t)
    (-> syntax? τ? syntax?)
    (match-let-values ([(_ e-) (τ⇐/λ! e t '())])
      e-))

  (define/contract (τ⇒app! e_fn t_fn e_arg #:src src)
    (-> syntax? τ? syntax? #:src syntax? (values syntax? τ?))
    (match t_fn
      [(τ:var^ x^)
       (let ([x1^ (generate-temporary x^)]
             [x2^ (generate-temporary x^)])
         (modify-type-context #{append % (list (ctx:var^ x2^) (ctx:var^ x1^) (ctx:solution x^ (τ:->* (τ:var x1^) (τ:var x2^))))})
         (values (quasisyntax/loc src
                   (lazy- (#%app- (force- #,e_fn) #,(τ⇐! e_arg (τ:var^ x1^)))))
                 (τ:var^ x2^)))]
      [(τ:->* a b)
       (values (quasisyntax/loc src
                 (lazy- (#%app- (force- #,e_fn) #,(τ⇐! e_arg a))))
               b)]
      [(τ:∀ x t)
       (let ([x^ (generate-temporary x)])
         (modify-type-context #{snoc % (ctx:var^ x^)})
         (τ⇒app! e_fn (inst t x (τ:var^ x^)) e_arg #:src src))]
      [(τ:qual constr t)
       (τ⇒app! (quasisyntax/loc src
                 (lazy- (#%app- (force- #,e_fn)
                                #,(quasisyntax/loc src
                                    (@%dictionary-placeholder
                                     #,(preservable-property->expression constr))))))
               t e_arg #:src src)]
      [_ (raise-syntax-error #f (format "cannot apply expression of type ~a to expression ~a"
                                        (τ->string t_fn) (syntax->datum e_arg))
                             e_arg)]))

  (define/contract (τs⇒! es)
    (-> (listof syntax?) (values (listof syntax?) (listof τ?)))
    (for/fold ([es- '()]
               [ts '()])
              ([e (in-list es)])
      (let-values ([(e- t) (τ⇒! e)])
        (values (snoc es- e-) (snoc ts t)))))

  (define/contract (elaborate-dictionaries stx)
    (-> syntax? syntax?)
    (syntax-parse stx
      #:context 'elaborate-dictionaries
      #:literals [#%plain-app @%dictionary-placeholder @%with-dictionary]
      [(#%plain-app @%dictionary-placeholder constr-expr)
       #:with this #`(quote-syntax #,this-syntax)
       #'(let-syntax-
          ([dict-expr
            (let*-values ([(constr) constr-expr]
                          [(instance constrs) (lookup-instance! constr #:src this)]
                          [(dict-id) (class:instance-dict-id instance)])
              ; It’s possible that the dictionary itself requires dictionaries for classes with
              ; subgoals, like (instance ∀ [a] [(Show a)] => (Show (List a)) ...). If there are not
              ; any constraints, we should just produce a bare identifier. Otherwise, we should
              ; produce an application to sub-dictionaries, which need to be recursively elaborated.
              (if (empty? constrs)
                  (make-rename-transformer dict-id)
                  (make-variable-like-transformer
                   (elaborate-dictionaries
                    (local-expand #`(#,dict-id #,@(for/list ([constr (in-list constrs)])
                                                    (quasisyntax/loc this
                                                      (@%dictionary-placeholder
                                                       #,(preservable-property->expression constr)))))
                                  'expression '())))))])
           dict-expr)]
      [(#%plain-app @%with-dictionary constr-expr e)
       #:with this #`(quote-syntax #,this-syntax)
       #:with dict-id (generate-temporary #'constr-expr)
       #'(λ- (dict-id)
           (let-syntax-
            ([abs-expr
              (match-let* ([(constr:class class-id t) constr-expr]
                           [class-info (syntax-local-value class-id)]
                           [instance (class:instance class-info (apply-current-subst t) #'dict-id)])
                (make-variable-like-transformer
                 (parameterize ([local-class-instances (cons instance (local-class-instances))])
                   (let ([elaborated (elaborate-dictionaries (quote-syntax e))])
                     (local-expand elaborated 'expression '())))))])
            abs-expr))]
      [(a . b)
       (datum->syntax this-syntax
                      (cons (elaborate-dictionaries #'a) (elaborate-dictionaries #'b))
                      this-syntax
                      this-syntax)]
      [_ this-syntax])))

(define-syntax-parser @%datum
  [(_ . n:integer)
   (attach-type #'(#%datum . n) (parse-type #'Integer))]
  [(_ . s:str)
   (attach-type #'(#%datum . s) (parse-type #'String))]
  [(_ . x)
   (raise-syntax-error #f "literal not supported" #'x)])

(define-syntax-parser :
  [(_ e t-expr:type)
   (attach-type (τ⇐! #'e (attribute t-expr.τ)) (apply-current-subst (attribute t-expr.τ)))])

(define-syntax-parser :/top-level
  [(_ e t-expr:type)
   #:with e- (local-expand #'(: e t-expr) 'expression '())
   (elaborate-dictionaries #'e-)])

(define-syntax-parser with-dictionary-elaboration
  [(_ e:expr)
   (~> #'e
       (local-expand 'expression '())
       elaborate-dictionaries
       (local-expand 'expression '()))])

(define-syntax-parser λ1
  [(_ x:id e:expr)
   #:do [(define t (get-expected this-syntax))]
   #:fail-unless t "no expected type, add more type annotations"
   #:fail-unless (τ:->? t) (format "expected ~a, given function" (τ->string t))
   #:do [(match-define (τ:->* a b) t)
         (modify-type-context #{snoc % (ctx:assump #'x a)})
         (define-values [xs- e-] (τ⇐/λ! #'e b (list (cons #'x a))))
         (modify-type-context #{ctx-remove % (ctx:assump #'x a)})]
   #:with [x-] xs-
   (attach-type #`(λ- (x-) #,e-) t)]
  [(_ x:id e:expr)
   #:do [(define x^ (generate-temporary))
         (define y^ (generate-temporary))
         (modify-type-context #{append % (list (ctx:var^ x^) (ctx:var^ y^) (ctx:assump #'x (τ:var^ x^)))})
         (define-values [xs- e-] (τ⇐/λ! #'e (τ:var^ y^) (list (cons #'x (τ:var^ x^)))))
         (modify-type-context #{ctx-remove % (ctx:assump #'x (τ:var^ x^))})]
   #:with [x-] xs-
   (attach-type #`(λ- (x-) #,e-) (τ:->* (τ:var^ x^) (τ:var^ y^)))])

(define-syntax (@%app stx)
  (if (type-transforming?)
      (syntax-parse stx
        [(_ a:type b:type)
         (τ-stx-token (τ:app (attribute a.τ) (attribute b.τ)))])
      (syntax-parse stx
        [(_ f:expr e:expr)
         #:do [(define-values [f- t_f] (τ⇒! #'f))
               (define-values [r- t_r] (τ⇒app! f- (apply-current-subst t_f) #'e
                                               #:src this-syntax))]
         (attach-type r- t_r)])))

(define-syntax-parser def
  #:literals [:]
  [(_ id:id
      {~or {~once {~seq : t:type}}
           {~optional fixity:fixity-annotation}}
      ...
      e:expr)
   #:with id- (generate-temporary #'id)
   #:with id/prefix (generate-temporary #'id)
   #:with t-expr (preservable-property->expression (attribute t.τ))
   #`(begin-
       (define- id- (:/top-level e t))
       #,(indirect-infix-definition
          #'(define-syntax- id (make-typed-var-transformer #'id- t-expr))
          (attribute fixity.fixity)))]
  [(_ id:id
      {~optional {~optional fixity:fixity-annotation}}
      e:expr)
   #:do [(define-values [e-stx- t]
           (let-values ([(e-stx- t) (τ⇒! #'e)])
             (values e-stx- (apply-current-subst t))))]
   #:with id- (generate-temporary #'id)
   #:with id/prefix (generate-temporary #'id)
   #:with e- (elaborate-dictionaries e-stx-)
   #:with t-expr (preservable-property->expression (generalize t))
   #'(begin-
       (define- id- e-)
       #,(indirect-infix-definition
          #'(define-syntax- id
              (make-typed-var-transformer #'id- t-expr))
          (attribute fixity.fixity)))])

(define-syntax-parser :infer/print-type
  [(_ e)
   (~> (τ⇒! #'e)
       (λ () _)
       (call-with-values _ list)
       second
       apply-current-subst
       τ->string
       displayln)
   #'(void)])

(define-syntax-parser @%top-interaction
  [(_ . e)
   (define-values [e- τ_e] (τ⇒! #'e))
   (printf ": ~a\n" (τ->string (apply-current-subst τ_e)))
   (elaborate-dictionaries e-)])
