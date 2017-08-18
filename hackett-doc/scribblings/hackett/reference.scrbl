#lang scribble/manual

@(require scribblings/hackett/private/util)

@title[#:tag "reference" #:style 'toc]{The Hackett Reference}

This section provides reference-style documentation for all of the bindings provided by @hash-lang[]
@racketmodname[hackett] and other built-in libraries. It is arranged by module, not by topic. For a
gentler, more tutorial-style introduction to Hackett and its features, see @secref["guide"].

@local-table-of-contents[]

@;{

@section[#:tag "reference-language-model"]{Language Model}

Hackett is a statically-typed, pure, lazy programming language. This section describes, in detail, how
Hackett’s value model and typechecker work. Much of the information in this section is more low-level
than most Hackett users will ever need to know about, and it should be used as a reference only when
necessary. For a friendlier overview of Hackett as a language, see @secref["guide"].

@subsection[#:tag "reference-value-model"]{Values and Evaluation}

@subsection[#:tag "reference-typechecking"]{The Typechecker}

In Hackett, typechecking occurs as part of macro @tech/racket-reference{expansion}. Hackett’s core
forms and primitives attach types to expressions’ @tech/racket-reference{syntax objects} during
expansion using certain @tech/racket-reference{syntax properties}, and those syntax properties are
inspected and propagated as a program expands. If a type error occurs during this process, a syntax
error is raised, and expansion halts.

}

@section[#:tag "reference-syntactic-forms"]{Core Syntactic Forms}

@subsection[#:tag "reference-type-annotation"]{Type Annotation}

@defform[(: expr type)]{

Annotates @racket[expr] with @racket[type]. If @racket[expr] does not have the given type, a type
error is produced.

@(hackett-examples
  #:no-preserve-source-locations
  (: 42 Integer)
  (: "hello" String)
  (eval:error (: "hello" Integer)))

Additionally, some forms (such as @racket[def] and @racket[defn]) recognize literal uses of @racket[:]
to provide additional locations for type annotations.}

@subsection[#:tag "reference-definitions"]{Definitions}

@defform[#:literals [: left right]
         (def id maybe-type maybe-fixity-ann val-expr)
         #:grammar
         ([maybe-type (code:line : type)
                      (code:line)]
          [maybe-fixity-ann (code:line #:fixity fixity)
                            (code:line)]
          [fixity left right])]{

Hackett’s basic definition form. Defines a new binding named @racket[id] with the value
@racket[val-expr]. If @racket[type] is provided, it is used as the type for @racket[id], and
@racket[val-expr]’s type is checked against the annotation. Otherwise, a type for @racket[id] is
inferred from @racket[val-expr].

@(hackett-examples
  #:no-preserve-source-locations
  (def x 7)
  (eval:check x 7)
  (def y : Integer 7)
  (eval:error (def z : String 7)))

If @racket[fixity] is specified, it defines @racket[id]’s @tech{operator fixity} when used as an
@tech{infix operator}.

@(hackett-examples
  (def -/right #:fixity right -)
  {10 -/right 15 -/right 6})}

@defform[#:literals [: left right]
         (defn id maybe-type maybe-fixity-ann
           [[arg-pat ...+] body-expr] ...+)
         #:grammar
         ([maybe-type (code:line : type)
                      (code:line)]
          [maybe-fixity-ann (code:line #:fixity fixity)
                            (code:line)]
          [fixity left right])]{

A shorthand definition form for defining a function with multiple cases. Essentially equivalent to the
following combination of @racket[def], @racket[lambda], and @racket[case*]:

@(racketblock
  (def id maybe-type
    (lambda [_arg ...]
      (case* [_arg ...]
        [[arg-pat ...] body-expr] ...))))

The @racket[defn] form is generally preferred when defining top-level functions.

@(hackett-examples
  (defn square : (-> Integer Integer)
    [[x] {x * x}])
  (eval:check (square 5) 25))}

@subsection[#:tag "reference-anonymous-functions"]{Anonymous Functions}

@deftogether[
 [@defform[(lambda [arg-pat ...+] body-expr)]
  @defform[(λ [arg-pat ...+] body-expr)]]]{

Produces a @tech{curried} function. The curried arity of the produced function will be the same as the
number of @racket[arg-pat]s provided. When the function is applied, the provided arguments will be
matched against each @racket[arg-pat], and the function’s result will be @racket[body-expr].

@(hackett-examples
  (eval:check ((λ [x y] {x + {y * 2}}) 5 10) 25))}

@deftogether[
 [@defform[(lambda* [[arg-pat ...+] body-expr] ...+)]
  @defform[(λ* [[arg-pat ...+] body-expr] ...+)]]]{

Produces a @tech{curried} function with multiple cases. Essentially equivalent to the following
combination of @racket[lambda] and @racket[case*]:

@(racketblock
  (lambda [_arg ...]
    (case* [_arg ...]
      [[arg-pat ...] body-expr] ...)))

@(hackett-examples
  (eval:check ((λ* [[(just x)] x]
                   [[nothing] 0])
               (just 42))
              42))}

@subsection[#:tag "reference-pattern-matching"]{Pattern Matching}

@defform[(case val-expr
           [pat body-expr] ...+)]{

Matches @racket[val-expr] against each @racket[pat], in order. The result of the expression is the
result of the @racket[body-expr] for the first matching @racket[pat].

@(hackett-examples
  (eval:check (case (just 42)
                [(just x) x]
                [nothing 0])
              42))}

@defform[(case* [val-expr ...+]
           [[pat ...+] body-expr] ...+)]{

Like @racket[case], but matches against multiple values at once. Each case only succeeds if @emph{all}
@racket[pat]s succeed.

@(hackett-examples
  (eval:check (case* [(just 1) (just 2)]
                [[(just _) nothing] "first"]
                [[nothing (just _)] "second"]
                [[(just _) (just _)] "both"]
                [[nothing nothing] "neither"])
              "both"))}

@section[#:tag "reference-datatypes"]{Datatypes}

@subsection[#:tag "reference-algebraic-datatypes"]{Defining algebraic datatypes}

@(define data-examples-eval (make-hackett-eval))
@defform[#:literals [left right]
         (data type-clause data-clause ...)
         #:grammar
         ([type-clause type-id
                       (code:line (type-constructor-id param-id ...+) maybe-fixity-ann)
                       (code:line {param-id type-constructor-id param-id} maybe-fixity-ann)]
          [data-clause value-id
                       (code:line (data-constructor-id arg-type ...+) maybe-fixity-ann)
                       (code:line {arg-type data-constructor-id arg-type} maybe-fixity-ann)]
          [maybe-fixity-ann (code:line #:fixity fixity)
                            (code:line)]
          [fixity left right])]{

Defines a new @deftech{algebraic datatype}. The defined type is distinct from all other types, whether
or not they have the same shape or name.

If @racket[type-clause] is a bare @racket[type-id], then @racket[type-id] is defined and bound
directly to the freshly defined type. Alternatively, @racket[type-constructor-id] may be provided,
which binds @racket[type-constructor-id] to a @tech{type constructor} that accepts the same number of
arguments as @racket[param-id]s are provided and constructs the freshly defined type when fully
saturated.

The fresh type is @emph{only} inhabited by the values defined and produced by the specified
@racket[data-clause]s. Specifically, each @racket[value-id] is bound to a unique value of the newly
defined type. Similarly, each @racket[data-constructor-id] is bound to a function that accepts
arguments with types @racket[arg-type]s and @emph{constructs} a value of the newly defined type that
contains the provided values.

@(hackett-examples
  #:eval data-examples-eval
  (data Foo
    (foo1 Integer Bool)
    (foo2 String)
    foo3)
  foo1
  (foo1 42 true)
  foo2
  (foo2 "hello")
  foo3)

Additionally, the bound @racket[value-id]s and @racket[data-constructor-id]s serve as @tech{patterns}
that match against different values of the defined type. The pattern associated with each
@racket[data-constuctor-id] accepts patterns that match against the contained values, so
pattern-matching allows extracting values stored “inside” data constructors.

@(hackett-examples
  #:eval data-examples-eval
  (case (foo1 42 true)
    [(foo1 n _) n]
    [(foo2 _)   2]
    [foo3       3]))

Like @racket[def], @racket[data] supports @tech{operator fixity} annotations. Each @racket[fixity]
specified controls the fixity used by the associated @racket[type-constructor-id] or
@racket[value-constructor-id] when used as an @tech{infix operator}.

@(hackett-examples
  (data (Tree a)
    {(Tree a) :&: (Tree a)} #:fixity right
    (leaf a))
  {(leaf 1) :&: (leaf 2) :&: (leaf 3)})}
@(close-eval data-examples-eval)

@subsection[#:tag "reference-numbers"]{Numbers}

@defidform[#:kind "type" Integer]{

The type of arbitrary-precision integers. Just as with numbers in @hash-lang[] @racketmodname[racket],
integers will be represented as @tech[#:doc '(lib "scribblings/reference/reference.scrbl")]{fixnums},
machine integers, where possible. Values that exceed this range will automatically be promoted to
arbitrary-precision “bignums”.}

@deftogether[
 [@defthing[+ {Integer -> Integer -> Integer}]
  @defthing[- {Integer -> Integer -> Integer}]
  @defthing[* {Integer -> Integer -> Integer}]]]{

These functions provide simple, arbitrary-precision, integral arithmetic.}

@defidform[#:kind "type" Double]{

The type of double-precision IEEE 754 floating-point numbers, known as
@tech[#:doc '(lib "scribblings/reference/reference.scrbl")]{flonums} in @hash-lang[]
@racketmodname[racket].}

@deftogether[
 [@defthing[d+ {Double -> Double -> Double}]
  @defthing[d- {Double -> Double -> Double}]
  @defthing[d* {Double -> Double -> Double}]
  @defthing[d/ {Double -> Double -> Double}]]]{

These functions provide simple, floating-point arithmentic on @racket[Double]s.}

@subsection[#:tag "reference-strings"]{Strings}

@defidform[#:kind "type" String]{

The type of strings, which can be constructed using string literals.}

@subsection[#:tag "reference-functions"]{Functions}

@defform[#:kind "type constructor" (-> a b)]{

A type constructor of arity 2 that represents functions, where @racket[a] is the type of value the
function accepts as an argument, and @racket[b] is the type of the result. Functions of higher arities
are represented via @tech[#:key "curried"]{currying}.}

@defthing[id (forall [a] {a -> a})]{

The identity function. Returns its argument unchanged.}

@defthing[const (forall [a b] {a -> b -> a})]{

Accepts two arguments and returns the first, ignoring the second.

@(hackett-examples
  (eval:check (const "hello" "goodbye") "hello")
  (eval:check (const unit (error! "never gets here")) unit))}

@subsection[#:tag "reference-quantification"]{Quantification and Constrained Types}

@deftogether[
 [@defform*[#:literals [=>]
            [(forall [var-id ...+] type)
             (forall [var-id ...+] constraint ...+ => type)]]
  @defform*[#:literals [=>]
            [(∀ [var-id ...+] type)
             (∀ [var-id ...+] constraint ...+ => type)]]]]{

Universal quantification over types. Within @racket[type], each @racket[var-id] is bound to a fresh,
universally quantified type.

The second form is a shorthand that provides a nicer syntax for types constructed with @racket[=>]
nested immediately within @racket[forall]: @racket[(forall [var-id ...] constraint ... => type)] is
precisely equivalent to @racket[(forall [var-id ...] (=> [constraint ...] type))].}

@defform[(=> [constraint ...+] type)]{

Builds a type that includes typeclass constraints. The resulting type is equivalent to @racket[type],
with the requirement that each @racket[constraint] must hold.}

@subsection[#:tag "reference-unit"]{Unit}

@defdata[Unit unit]{

The unit type. Values of type @racket[Unit] only have one possible value (ignoring @tech{bottom}),
@racket[unit]. A value of type @racket[unit] carries no information, so it is similar to @void-const
in @hash-lang[] @racketmodname[racket] or the @tt{void} return “type” in many C-like languages.}

@subsection[#:tag "reference-booleans"]{Booleans}

@defdata[Bool true false]{

The boolean type, representing two binary states.}

@defthing[not {Bool -> Bool}]{

Inverts the value it is applied to; that is, produces @racket[false] when given @racket[true] and
produces @racket[true] when given @racket[false].}

@subsection[#:tag "reference-optionals"]{Optionals}

@defdata[(Maybe a) (just a) nothing]{

A type that encodes the notion of an optional or nullable value. A value of type @racket[(Maybe a)]
implies that it @emph{might} contain a value of type @racket[a], but it also might contain nothing at
all. This type is usually used to represent operations that can fail (where @racket[nothing]
represents failure) or values that are not required to be present.}

@subsection[#:tag "reference-lists"]{Lists}

@defdata[(List a) (:: a (List a)) nil]{

The @deftech{list} type, which describes lazy linked lists. Since a list is lazy, it may be infinite,
as long as the entire list is never demanded. The @racket[::] constructor is pronounced “cons”, and it
is generally intended to be used infix.}

@section[#:tag "reference-controlling-evaluation"]{Controlling Evaluation}

@defthing[seq (forall [a b] {a -> b -> b})]{

Accepts two arguments and returns its second argument. When the result is forced, the first argument
will also be evaluated to weak head normal form. This can be used to reduce laziness.}

@defthing[error! (forall [a] {String -> a})]{

A simple @tech{partial function} that crashes the program with a message when evaluated.}

@defthing[undefined! (forall [a] a)]{

A @tech[#:key "partial function"]{partial} value that crashes the program when evaluated.}
