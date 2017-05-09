#lang curly-fn racket/base

(require racket/require hackett/private/util/require)

(require (for-syntax (multi-in racket [base format syntax])
                     (multi-in syntax/parse [class/local-value experimental/specialize])

                     hackett/private/util/stx)

         (postfix-in - (multi-in racket [base splicing]))
         syntax/parse/define

         hackett/private/base)

(provide data)

(begin-for-syntax
  (define-syntax-class type-constructor-spec
    #:attributes [tag [arg 1] len nullary?]
    #:description #f
    [pattern tag:id
             #:attr [arg 1] '()
             #:attr len 0
             #:attr nullary? #t]
    [pattern (tag:id arg:id ...+)
             #:attr len (length (attribute arg))
             #:attr nullary? #f]
    [pattern {~and (tag:id)
                   {~fail (~a "types without arguments should not be enclosed in parentheses; perhaps"
                              " you meant ‘" (syntax-e #'tag) "’?")}}
             #:attr [arg 1] #f
             #:attr len #f
             #:attr nullary? #f])

  (define-syntax-class data-constructor-spec
    #:attributes [tag [arg 1] len nullary?]
    #:description #f
    [pattern tag:id
             #:attr [arg 1] '()
             #:attr len 0
             #:attr nullary? #t]
    [pattern (tag:id arg ...+)
             #:attr len (length (attribute arg))
             #:attr nullary? #f]
    [pattern {~and (tag:id)
                   {~fail (~a "data constructors without arguments should not be enclosed in "
                              "parentheses; perhaps you meant ‘" (syntax-e #'tag) "’?")}}
             #:attr [arg 1] #f
             #:attr len #f
             #:attr nullary? #f])

  (struct data-constructor (macro type)
    #:property prop:procedure 0)

  (define-syntax-class/specialize data-constructor-val
    (local-value data-constructor? #:failure-message "not bound as a data constructor")))

(define-syntax-parser define-data-constructor
  [(_ τ:type-constructor-spec constructor:data-constructor-spec)
   #:with tag- (generate-temporary #'constructor.tag)
   #:with tag-/curried (generate-temporary #'constructor.tag)
   #:with [α ...] (attribute τ.arg)
   ; calculate the result type of the data constructor, after being applied to args (if any)
   #:with τ_result (if (attribute τ.nullary?) #'τ.tag #'(τ.tag α ...))
   ; calculate the type of the underlying constructor, with arguments, unquantified
   #:with τ_con_unquantified (foldr #{begin #`(-> #,%1 #,%2)} #'τ_result (attribute constructor.arg))
   ; quantify the type using the type variables in τ, then evaluate the type
   #:with τ_con:type (foldr #{begin #`(∀ #,%1 #,%2)} #'τ_con_unquantified (attribute α))
   #:with τ_con-expr (preservable-property->expression (attribute τ_con.τ))
   #:with [field ...] (generate-temporaries (attribute constructor.arg))
   ; check if the constructor is nullary or not
   (if (attribute constructor.nullary?)
       ; if it is, just define a value
       #'(begin-
           (define- tag-
             (let- ()
               (struct- constructor.tag ())
               (constructor.tag)))
           (define-syntax- constructor.tag
             (data-constructor (make-typed-var-transformer #'tag- τ_con-expr) τ_con-expr)))
       ; if it isn’t, define a constructor function
       #`(splicing-local- [(struct- tag- (field ...) #:transparent
                             #:reflection-name 'constructor.tag)
                           (define- #,(foldl #{begin #`(#,%2 #,%1)} #'tag-/curried (attribute field))
                             (tag- field ...))]
           (define-syntax- constructor.tag
             (data-constructor (make-typed-var-transformer #'tag-/curried τ_con-expr) τ_con-expr))))])

(define-syntax-parser data
  [(_ τ:type-constructor-spec constructor:data-constructor-spec ...)
   #:with τ-base (generate-temporary #'τ.tag)
   #:with [τ-arg ...] (generate-temporaries (attribute τ.arg))
   #:with [τ-arg.τ ...] (map #{begin #`(attribute #,(format-id % "~a.τ" %))} (attribute τ-arg))
   #`(begin-
       (define-for-syntax- τ-base (τ:con #'τ.tag))
       (define-syntax-parser τ.tag
         #,(if (attribute τ.nullary?)
               #'[_:id (τ-stx-token τ-base)]
               #`[(_ {~var τ-arg type} ...)
                  (τ-stx-token #,(foldl #{begin #`(τ:app #,%2 #,%1)} #'τ-base (attribute τ-arg.τ)))]))
       (define-data-constructor τ constructor) ...)])
