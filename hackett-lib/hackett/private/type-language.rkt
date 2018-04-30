#lang racket/base

; This module defines Hackett’s type-level language, which is entirely separate from its value-level
; language. Types, like expressions, are represented by syntax objects, and also like expressions,
; types are expanded by the macroexpander. The typechecker operates exclusively on fully-expanded
; types.

(require (for-meta 2 racket/base

                     hackett/private/util/stx)
         (for-syntax racket/base
                     racket/syntax
                     syntax/intdef
                     syntax/parse/define
                     syntax/parse/experimental/template
                     threading

                     hackett/private/util/stx)
         syntax/parse/define)

(provide (for-syntax type-literal-ids type-literals type expand-type
                     ~#%type:app* ~#%type:app+ ?#%type:app*
                     ~#%type:forall* ?#%type:forall* ~#%type:qual* ?#%type:qual*
                     ~-> ~->* ~->+ ?->*
                     value-namespace-introduce type-namespace-introduce ~type)
         #%type:con #%type:app #%type:forall #%type:qual
         #%type:bound-var #%type:wobbly-var #%type:rigid-var
         #%forall define-base-type ->
         begin-for-value begin-for-type)

;; ---------------------------------------------------------------------------------------------------
;; fully-expanded types

; All types in the type language eventually desugar to a kernel language made up of a small number of
; primitive forms; these core forms are defined here. They have no useful bindings because they cannot
; be meaningfully expanded; like Racket’s own #%plain-app and other #%kernel forms are recognized by
; the compiler, Hackett’s kernel type language includes kernel forms that are recognized by the
; typechecker.

(define-syntaxes
  [; (#%type:con id)
   ;
   ; Type constructors, the primary building block that all concrete types are built out of. Type
   ; constructors may actually be types themselves (such as Unit, Integer, or String), or they may be
   ; “type functions” that accept other types to produce a concrete type (such as Tuple, Maybe, or
   ; List).
   #%type:con

   ; (#%type:app type type)
   ;
   ; Type application, which represents the application of some type constructor to type arguments.
   ; For example, (Maybe Integer) is the application of the Maybe constructor to the Integer
   ; constructor. Type constructors are curried in the same way that value-level functions are, so
   ; type applications can be nested in a left-associative manner to represent applying a type to
   ; multiple arguments.
   #%type:app

   ; (#%type:forall id type)
   ;
   ; Universal quantification over types. The primitive quantifier abstracts a single type variable
   ; within its type. Within t, (type:bound-var x) may appear.
   #%type:forall

   ; (#%type:qual type type)
   ;
   ; Qualified types, aka types with constraints. Currently, the only sort of constraint Hackett
   ; supports is typeclass constraints. Constraints themselves are represented as types, though they
   ; do not (directly) describe any terms. Typeclass names may serve as type constructors that can be
   ; applied to other types just like any others.
   #%type:qual

   ; (#%type:bound-var id)
   ;
   ; Bound type variables. In the type (forall [a] a), a is a bound-var until the forall is
   ; instantiated. These usually do not appear in typechecking (since they will be instantiated to
   ; wobbly-var, rigid-var, or a concrete type).
   #%type:bound-var

   ; (#%type:wobbly-var id)
   ;
   ; Solver, aka “wobbly” variables, which represent some yet-unknown type. The typechecker will
   ; solve these variables as necessary as part of unification.
   #%type:wobbly-var

   ; (#%type:rigid-var id)
   ;
   ; Rigid, aka “skolem”, type variables, which represent a *specific* unknown type. While solver
   ; variables unify with *anything*, rigid type variables unify with *nothing* (except themselves).
   ; These are introduced by user-provided type annotations — for example, an identity function
   ; annotated with (forall [a] {a -> a}) will check the implementation against a fresh rigid variable
   ; for a.
   ;
   ; Since rigid type variables are completely unique, this process ensures an implementation is
   ; suitably polymorphic. If a function typechecks with a rigid type variable, it must work for *all*
   ; types, since the function cannot know anything about the type. This is in contrast to an ordinary
   ; solver variable: if we used a solver variable to check the identity function instead of a rigid
   ; variable, then the user could write code that would get the solver variable to unify with a
   ; single, concrete type (such as (λ [x] {x + 1})), which would defeat the whole point of the
   ; quantified type annotation.
   #%type:rigid-var]

  (let ([type-literal (λ (stx) (raise-syntax-error #f "cannot be used as an expression" stx))])
    (values type-literal type-literal type-literal type-literal
            type-literal type-literal type-literal)))

(begin-for-syntax
  (define type-literal-ids
    (list #'#%type:con #'#%type:app #'#%type:forall #'#%type:qual
          #'#%type:bound-var #'#%type:wobbly-var #'#%type:rigid-var))
  (define-literal-set type-literals
    [#%type:con #%type:app #%type:forall #%type:qual
     #%type:bound-var #%type:wobbly-var #%type:rigid-var]))

;; ---------------------------------------------------------------------------------------------------
;; type expansion

(begin-for-syntax
  (define-syntax-class (type [intdef-ctx #f])
    #:description "type"
    #:attributes [expansion residual]
    [pattern _ #:with {~var || (expanded-type intdef-ctx)}
                      (local-expand this-syntax 'expression type-literal-ids intdef-ctx)])

  (define-syntax-class (expanded-type intdef-ctx)
    #:description #f
    #:attributes [expansion residual]
    #:commit
    #:literal-sets [kernel-literals type-literals]
    [pattern (head:#%expression ~! {~var a (type intdef-ctx)})
             #:attr expansion (syntax-track-origin #'a.expansion this-syntax #'head)
             #:attr residual (~> #'(values)
                                 (syntax-track-origin #'a.residual #'head)
                                 (syntax-track-origin #'expansion #'head))]
    [pattern (head:#%type:con ~! _:id)
             #:attr expansion this-syntax
             #:attr residual (syntax-track-origin #'(values) this-syntax #'head)]
    [pattern (head:#%type:app ~! {~var a (type intdef-ctx)} {~var b (type intdef-ctx)})
             #:attr expansion (syntax/loc/props this-syntax
                                (head a.expansion b.expansion))
             #:attr residual (~> #'(values)
                                 (syntax-track-origin #'a.residual #'head)
                                 (syntax-track-origin #'b.residual #'head)
                                 (syntax-track-origin #'expansion #'head))]
    [pattern (head:#%type:forall ~! x:id {~var t (type intdef-ctx)})
             #:attr expansion (syntax/loc/props this-syntax
                                (head x t.expansion))
             #:attr residual (~> #'(values)
                                 (syntax-track-origin #'t.residual #'head)
                                 (syntax-track-origin #'expansion #'head))]
    [pattern (head:#%type:qual ~! {~var a (type intdef-ctx)} {~var b (type intdef-ctx)})
             #:attr expansion (syntax/loc/props this-syntax
                                (head a.expansion b.expansion))
             #:attr residual (~> #'(values)
                                 (syntax-track-origin #'a.residual #'head)
                                 (syntax-track-origin #'b.residual #'head)
                                 (syntax-track-origin #'expansion #'head))]
    [pattern (head:#%type:bound-var ~! _:id)
             #:attr expansion this-syntax
             #:attr residual (syntax-track-origin #'(values) this-syntax #'head)]
    [pattern (head:#%type:wobbly-var ~! _:id)
             #:attr expansion this-syntax
             #:attr residual (syntax-track-origin #'(values) this-syntax #'head)]
    [pattern (head:#%type:rigid-var ~! _:id)
             #:attr expansion this-syntax
             #:attr residual (syntax-track-origin #'(values) this-syntax #'head)]
    [pattern (head:letrec-syntaxes+values ~! ([(id:id ...) e:expr] ...) () t:expr)
             #:do [(define intdef-ctx* (syntax-local-make-definition-context intdef-ctx))
                   (for ([ids (in-list (attribute id))]
                         [e (in-list (attribute e))])
                     (syntax-local-bind-syntaxes ids e intdef-ctx*))]
             #:with {~var t- (type intdef-ctx*)} #'t
             #:attr expansion (internal-definition-context-track intdef-ctx* #'t-.expansion)
             #:attr residual (~> #'(values)
                                 (syntax-track-origin #'t-.residual #'head)
                                 (syntax-track-origin #'expansion #'head))])

  (define expand-type
    (syntax-parser
      #:context 'expand-type
      [t:type #'t.expansion])))

; Expanding #%type:forall multiple times should be idempotent, so it can’t do variable renaming on its
; own. Instead, this slightly higher-level macro performs the renaming.
(define-syntax-parser #%forall
  [(_ x:id t)
   #:with x- (generate-temporary #'x)
   #:do [(define intdef-ctx (syntax-local-make-definition-context))
         (syntax-local-bind-syntaxes (list #'x)
                                     #'(make-variable-like-transformer
                                        (quote-syntax (#%type:bound-var x-)))
                                     intdef-ctx)]
   #:with {~var t- (type intdef-ctx)} #'t
   (~>> (syntax/loc this-syntax
          (#%type:forall x- t-.expansion))
        (internal-definition-context-track intdef-ctx))])

;; ---------------------------------------------------------------------------------------------------
;; helper expanders / metafunctions

; This section provides syntax/parse pattern-expanders and syntax/parse/experimental/template
; metafunctions for parsing and creating fully-expanded types. It provides helpers to parse and
; produce nested type applications, so (#%type:app (#%type:app Either String) Integer) can be parsed
; or produced by writing the more direct forms {~#%type:app* a b c} and
; {?#%type:app Either String Integer}. Similar helpers are provided for nested foralls and nested
; qualifications.

(begin-for-syntax
  (define-syntax-class nested-apps
    #:description #f
    #:attributes [[linearized 1]]
    #:commit
    #:literal-sets [type-literals]
    [pattern (#%type:app ~! a:nested-apps b)
             #:with [linearized ...] #'[a.linearized ... b]]
    [pattern t #:with [linearized ...] #'[t]])

  (define-syntax ~#%type:app*
    (pattern-expander
     (syntax-parser
       [(_ . list-pat)
        #'{~and apps:nested-apps
                {~parse list-pat (attribute apps.linearized)}}])))

  (define-syntax ~#%type:app+
    (pattern-expander
     (syntax-parser
       [(_ . list-pat)
        #'{~#%type:app* . {~and [_ _ ...+] list-pat}}])))

  (define-template-metafunction ?#%type:app*
    (syntax-parser
      [(_ a) #'a]
      [(_ a b c ...)
       (quasitemplate/loc/props this-syntax
         (?#%type:app* #,(syntax/loc/props this-syntax
                           (#%type:app a b))
                       c ...))]))

  (define-syntax-class nested-foralls
    #:description #f
    #:attributes [[x 1] t]
    #:commit
    #:literal-sets [type-literals]
    [pattern (#%type:forall ~! x* t*:nested-foralls)
             #:with [x ...] #'[x* t*.x ...]
             #:with t #'t*.t]
    [pattern t
             #:with [x ...] #'[]])

  (define-syntax ~#%type:forall*
    (pattern-expander
     (syntax-parser
       [(_ list-pat pat)
        #'{~and foralls:nested-foralls
                {~parse list-pat (attribute foralls.x)}
                {~parse pat #'foralls.t}}])))

  (define-template-metafunction ?#%type:forall*
    (syntax-parser
      [(_ [] t) #'t]
      [(_ [a ... b] t)
       (quasitemplate/loc/props this-syntax
         (?#%type:forall* [a ...] #,(syntax/loc/props this-syntax
                                      (#%type:forall b t))))]))

  (define-syntax-class nested-quals
    #:description #f
    #:attributes [[x 1] t]
    #:commit
    #:literal-sets [type-literals]
    [pattern (#%type:qual ~! x* t*:nested-quals)
             #:with [x ...] #'[x* t*.x ...]
             #:with t #'t*.t]
    [pattern t
             #:with [x ...] #'[]])

  (define-syntax ~#%type:qual*
    (pattern-expander
     (syntax-parser
       [(_ list-pat pat)
        #'{~and foralls:nested-quals
                {~parse list-pat (attribute foralls.x)}
                {~parse pat #'foralls.t}}])))

  (define-template-metafunction ?#%type:qual*
    (syntax-parser
      [(_ [] t) #'t]
      [(_ [a ... b] t)
       (quasitemplate/loc/props this-syntax
         (?#%type:qual* [a ...] #,(syntax/loc/props this-syntax
                                    (#%type:qual b t))))])))

;; ---------------------------------------------------------------------------------------------------
;; defining base types

(begin-for-syntax
  (begin-for-syntax
    (define (make-type-con-pattern-expander con-id)
      (pattern-expander
       (syntax-parser
         [(head:id pat ...)
          (quasisyntax/loc this-syntax
            (~#%type:app* #,(quasisyntax/loc #'head
                              ({~literal #%type:con} {~literal #,con-id}))
                          pat ...))])))))

(define-simple-macro (define-base-type name:id)
  #:with {~var ~name} (format-id #'name "~~~a" #'name #:source #'name #:props #'name)
  ; Ensure that the binding does not have either the type or the value scope on it. Otherwise, if the
  ; type appears in a fully-expanded type or value, and the namespace on the resulting piece of syntax
  ; is flipped, the identifier can become unbound.
  #:with name- (datum->syntax #'here (syntax-e #'name) #'name)
  (begin
    (define-syntax name- (make-variable-like-transformer
                          (λ (name-id)
                            #`(#%type:con #,(replace-stx-loc (quote-syntax name-) name-id)))))
    (define-syntax name (make-rename-transformer #'name-))
    (begin-for-syntax
      (define-syntax ~name (make-type-con-pattern-expander (quote-syntax name))))))

;; ---------------------------------------------------------------------------------------------------
;; function types

; Functions are the only truly “baked-in” types, from the perspective of the typechecker. They are
; handled specially by the typechecker in order to implement higher-rank polymorphism, so they are
; defined here.

(define-base-type ->)

(begin-for-syntax
  (define-syntax-class nested-->s
    #:description #f
    #:attributes [[t 1]]
    #:commit
    #:literal-sets [type-literals]
    [pattern (~-> ~! a b:nested-->s)
             #:with [t ...] #'[a b.t ...]]
    [pattern a #:with [t ...] #'[a]])

  (define-syntax ~->*
    (pattern-expander
     (syntax-parser
       [(_ . list-pat)
        #'{~and ->s:nested-->s
                {~parse list-pat (attribute ->s.t)}}])))

  (define-syntax ~->+
    (pattern-expander
     (syntax-parser
       [(_ . list-pat)
        #'{~->* . {~and [_ _ ...+] list-pat}}])))

  (define-template-metafunction ?->*
    (syntax-parser
      [(_ a) #'a]
      [(head a b c ...)
       (quasitemplate/loc/props this-syntax
         (?#%type:app* #,(quasisyntax/loc #'head (#%type:con #,(syntax/loc #'head ->)))
                       a
                       (?->* b c ...)))])))

;; ---------------------------------------------------------------------------------------------------
;; type and value namespaces

; Hackett programs have two namespaces: types and values. These are represented by two syntax
; introducers, each with a unique scope. However, in order to properly cooperate with
; (module* _ #f ....) submodules, it’s important that the scopes are *global*; that is, they are
; shared across both module instantiations and bytecode marshalling/unmarshalling. For this, we use
; make-interned-syntax-introducer, which ensures the scope is always the same.

(begin-for-syntax
  (define value-introducer (make-interned-syntax-introducer 'hackett-value))
  (define type-introducer (make-interned-syntax-introducer 'hackett-type))

  (define value-namespace-introduce
    (λ~> (value-introducer 'add) (type-introducer 'remove)))

  (define type-namespace-introduce
    (λ~> (value-introducer 'remove) (type-introducer 'add)))

  (define-syntax ~type
    (pattern-expander
     (syntax-parser
       [(_ pat)
        #'{~and tmp {~parse pat (type-namespace-introduce #'tmp)}}]))))

(define-syntax-parser begin-for-value
  [(_ form ...)
   #:with [form* ...] (map value-namespace-introduce (attribute form))
   (syntax/loc this-syntax
     (begin form* ...))])

(define-syntax-parser begin-for-type
  [(_ form ...)
   #:with [form* ...] (map type-namespace-introduce (attribute form))
   (syntax/loc this-syntax
     (begin form* ...))])
