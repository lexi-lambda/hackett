#lang turnstile/lang

(provide (rename-out [app #%app])
         ∀
         Integer String Maybe

         let data)

(require (postfix-in - (combine-in racket/base
                                   racket/function
                                   racket/splicing)))

(define-syntax-category kind)
(define-base-kind ★)

(begin-for-syntax
  (current-type? (λ (τ) (kind? (typeof τ))))

  (define (syntax-properties stx)
    (map (λ (key) (cons key (syntax-property stx key)))
         (syntax-property-symbol-keys stx))))

(define-type-constructor →-
  #:arity = 2
  #:arg-variances (const (list covariant contravariant))
  #:no-attach-kind
  #:no-provide)

(define-kind-constructor ∀→ #:arity = 1 #:no-provide)
(define-type-constructor ∀- #:bvs = 1 #:arr ∀→ #:no-provide)

(define-typed-syntax →
  [(_ a:type b:type) ≫
   [⊢ a ≫ a- ⇐ ★]
   [⊢ b ≫ b- ⇐ ★]
   -------------------
   [⊢ (→- a- b-) ⇒ ★]])

(define-simple-macro (∀ [x:id {~datum :} k] τ)
  (∀- ([x : k]) τ))

;; ---------------------------------------------------------------------------------------------------

(define-typed-syntax λ
  #:datum-literals [:]
  [(_ [x:id : τ_in:type] expr) ≫
   [[x ≫ x- : τ_in.norm] ⊢ expr ≫ expr- ⇒ τ_out]
   -----------------------------------------------
   [⊢ (λ- (x-) expr-) ⇒ (→ τ_in.norm τ_out)]]
  [(_ x:id expr) ⇐ (~→- τ_in τ_out) ≫
   [[x ≫ x- : τ_in] ⊢ expr ≫ expr- ⇐ τ_out]
   ------------------------------------------
   [⊢ (λ- (x-) expr-)]])

(define-syntax-parser app
  #:datum-literals [@]
  ; type application
  [(_ fn @ . args)
   #'(app/τ fn . args)]
  ; term application
  [(_ fn . args)
   #'(app/e fn . args)])

(define-typed-syntax app/τ
  [(_ fn τ_arg:type) ≫
   [⊢ fn ≫ fn- ⇒ : (~∀- (τ_var) τ_body) (⇒ (~∀→ k))]
   [⊢ τ_arg ≫ τ_arg- ⇐ k]
   #:with τ_inst (subst #'τ_arg- #'τ_var #'τ_body)
   ------------------------------------------------
   [⊢ fn- ⇒ τ_inst]]
  [(_ fn τ_arg:type args ...+) ≫
   -----------------------------------
   [≻ (app (app/τ fn τ_arg) args ...)]])

(define-typed-syntax app/e
  [(_ fn arg) ≫
   [⊢ fn ≫ fn- ⇒ (~→- τ_in τ_out)]
   [⊢ arg ≫ arg- ⇐ τ_in]
   --------------------------------
   [⊢ (#%app- fn- arg-) ⇒ τ_out]]
  [(_ fn arg args ...+) ≫
   ---------------------------
   [≻ (app (app/e fn arg) args ...)]])

(define-typed-syntax Λ
  #:datum-literals [:]
  [(_ [α:id : k:kind] expr) ≫
   [[α ≫ α- : k.norm] ⊢ expr ≫ expr- ⇒ t]
   ---------------------------------------------------
   [⊢ expr- ⇒ (∀- ([α- : k.norm]) t)]])

(define-typed-syntax (ann e {~datum :} τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------------------
  [⊢ e- ⇒ τ.norm])

(define-typed-syntax def
  #:datum-literals [:]
  [(_ x:id : τ:type e:expr) ≫
   #:with y (generate-temporary #'x)
   ---------------------------------------
   [≻ (begin
        (define- y (ann e : τ.norm))
        (define-syntax x (make-variable-like-transformer (⊢ y : τ.norm))))]]
  [(_ x:id e:expr) ≫
   [⊢ e ≫ e- ⇒ τ]
   #:with y (generate-temporary #'x)
   ---------------
   [≻ (begin-
        (define- y e-)
        (define-syntax x (make-variable-like-transformer (⊢ y : τ))))]])

(define-typed-syntax let1
  #:datum-literals [:]
  [(_ [x:id : τ:type e_val:expr] e_body:expr) ≫
   #:with y (generate-temporary #'x)
   ---------------------------------
   [≻ (letrec-syntaxes+values ([(x) (make-variable-like-transformer (⊢ y : τ.norm))])
                              ([(y) (ann e_val : τ.norm)])
        e_body)]]
  [(_ [x:id e_val:expr] e_body:expr) ≫
   [⊢ e_val ≫ e_val- ⇒ τ]
   #:with y (generate-temporary #'x)
   ---------------------------------
   [≻ (letrec-syntaxes+values ([(x) (make-variable-like-transformer (⊢ y : τ))])
                              ([(y) (ann e_val : τ)])
        e_body)]])

(define-syntax-parser let
  [(_ (clause) body)
   #'(let1 clause body)]
  [(_ (clause clauses ...) body)
   #'(let1 clause (let (clauses ...) body))])

(define-typed-syntax letrec
  #:datum-literals [:]
  [(_ ([x:id : τ:type e_val:expr] ...) e_body:expr) ≫
   #:with (y ...) (generate-temporaries #'(x ...))
   -----------------------------------------------
   [≻ (letrec-syntaxes+values ([(x) (make-variable-like-transformer (⊢ y : τ.norm))] ...)
                              ([(y) (ann e_val : τ.norm)] ...)
        e_body)]])

;; ---------------------------------------------------------------------------------------------------

(define-simple-macro (define-base-type: τ {~datum :} k)
  #:with τ- (generate-temporary #'τ)
  (begin
    (define-base-type τ- #:no-attach-kind #:no-provide)
    (define-syntax τ (make-variable-like-transformer (⊢ τ- : k)))))

(define-kind-constructor →k
  #:arity = 2
  #:arg-variances (const (list covariant contravariant)))

(define-base-type: Integer : ★)
(define-base-type: String : ★)

(define-base-type: Maybe : (→k ★ ★))

(define-typed-syntax #%datum
  [(_ . n:integer) ≫
   ----------------------------
   [⊢ (#%datum- . n) ⇒ Integer]]
  [(_ . n:str) ≫
   ---------------------------
   [⊢ (#%datum- . n) ⇒ String]]
  [(_ . x) ≫
   ----------------------------------------------------------------------
   [_ #:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

;; ---------------------------------------------------------------------------------------------------

(define ((+ a) b) (+- a b))
(define ((- a) b) (-- a b))
(define ((* a) b) (*- a b))
(define ((/ a) b) (quotient- a b))

(define-primop + : (→ Integer (→ Integer Integer)))
(define-primop - : (→ Integer (→ Integer Integer)))
(define-primop * : (→ Integer (→ Integer Integer)))
(define-primop / : (→ Integer (→ Integer Integer)))

;; ---------------------------------------------------------------------------------------------------

(define-primop string-append : (→ String (→ String String)))

(define ((string-append a) b)
  (string-append- a b))

;; ---------------------------------------------------------------------------------------------------

(begin-for-syntax
  (define-syntax-class data-constructor-spec
    #:attributes [tag [arg 1] len nullary?]
    #:description #f
    [pattern tag:id
             #:attr [arg 1] #'()
             #:attr len 0
             #:attr nullary? #t]
    [pattern {~and norm (tag:id arg ...+)}
             #:attr len (length (attribute arg))
             #:attr nullary? #f]
    [pattern {~and (tag:id)
                   {~fail (~a "data constructors without arguments should not be enclosed in "
                              "parentheses; perhaps you meant ‘" (syntax-e #'tag) "’?")}}
             #:attr [arg 1] #f
             #:attr len #f
             #:attr nullary? #f]))

(define-syntax-parser →/autocurry
  [(_ τa τb) #'(→ τa τb)]
  [(_ τ τs ...+) #'(→ τ (→/autocurry τs ...))])

; helper macro for `data`
(define-syntax-parser define-data-constructor
  [(_ τ:id constructor:data-constructor-spec)
   #:with tag- (generate-temporary #'constructor.tag)
   #:with tag-/curried (generate-temporary #'constructor.tag)
   #:with [τ_arg:type ...] #'(constructor.arg ...)
   #:with [field ...] (generate-temporaries #'(constructor.arg ...))
   #`(begin-
       ; check if the constructor is nullary or not
       #,(if (attribute constructor.nullary?)
             ; if it is, just define a value
             #'(define- tag-
                 (let- ()
                   (struct- constructor.tag () #:transparent)
                   (constructor.tag)))
             ; if it isn’t, define a constructor function, but preserve the original `struct`-defined
             ; id as a syntax property (to be used with Racket’s `match`)
             #'(splicing-local- [(struct- tag- (field ...) #:transparent
                                   #:reflection-name 'constructor.tag)
                                 (define- tag-/curried (curry- tag-))]
                 (define-syntax constructor.tag
                   (make-variable-like-transformer
                    (syntax-property (⊢ tag-/curried : (→/autocurry τ_arg ... τ))
                                     'orig-constructor #'tag-))))))])

(define-syntax-parser data
  [(_ τ:id constructor:data-constructor-spec ...)
   #:with τ- (generate-temporary #'τ)
   #:with [tag- ...] (generate-temporaries #'(constructor.tag ...))
   #'(begin-
       (define-type-constructor τ-
         #:arity = 0
         #:no-attach-kind
         #:no-provide)
       (define-typed-syntax τ
         [:id ≫
          ------------
          [⊢ #,(syntax-property #'(τ-) 'constructors #'(constructor ...)) ⇒ ★]])
       (define-data-constructor τ constructor) ...)])

(define-typed-syntax case
  #:literals [quote-syntax]
  [(_ e_val:expr [tag:data-constructor-spec e_body:expr] ...+) ≫
   ; get the type we’re destructuring on
   [⊢ e_val ≫ e_val- ⇒ τ_val]
   #:fail-unless (get-stx-prop/car #'τ_val 'constructors)
                 (~a "cannot pattern match on value of type ‘" (type->str #'τ_val) "’ because it does"
                     " not have any visible constructors")
   #:with (constructor:data-constructor-spec ...)
          (get-stx-prop/car #'τ_val 'constructors)

   ; assert that all of the tags are actually constructors of τ_val
   #:do [(for ([given-constructor (in-list (attribute tag))]
               [given-tag (in-list (attribute tag.tag))])
           (unless (member given-tag (attribute constructor.tag) free-identifier=?)
             (raise-syntax-error #f (~a "‘" (syntax-e given-tag) "’ is not a visible constructor of ‘"
                                        (type->str #'τ_val) "’")
                                 this-syntax given-constructor)))]

   ; ensure that all the bodies produce the same type
   #:with [[binding-id:id ...] ...] #'((tag.arg ...) ...)
   #:with [[binding-type ...] ...] #'((constructor.arg ...) ...)
   [[binding-id ≫ binding-id- : binding-type] ... ⊢ e_body ≫ e_body- ⇒ τ_result] ...
   #:fail-unless (same-types? #'(τ_result ...))
                 "all clause bodies must produce the same type"
   #:with [τ_result* . _] #'(τ_result ...)

   ; perform exhaustiveness checking
   #:fail-unless (for/and ([constr-tag (in-list (attribute constructor.tag))])
                   (member constr-tag (attribute tag.tag) free-identifier=?))
                 (~a "not all cases of type ‘" (type->str #'τ_val) "’ are accounted for")

   #:with [tag-matcher ...] (map (λ (stx) (syntax-property (expand/df stx) 'orig-constructor))
                                 (attribute tag.tag))
   ---------------------------------------------------------------------------------------------------
   [⊢ (let- ([val e_val-])
        (match- val
          [(tag-matcher binding-id- ...) e_body-] ...))
      ⇒ τ_result*]])
