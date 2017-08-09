#lang scribble/manual

@(require scribblings/hackett/private/util)

@title[#:tag "reference" #:style 'toc]{The Hackett Reference}

This section provides reference-style documentation for all of the bindings provided by @hash-lang[]
@racketmodname[hackett] and other built-in libraries. It is arranged by module, not by topic. For a
gentler, more tutorial-style introduction to Hackett and its features, see @secref["guide"].

@local-table-of-contents[]

@section[#:tag "reference-syntactic-forms"]{Core Syntactic Forms}

@subsection[#:tag "reference-type-annotation"]{Type Annotation}

@defform[(: expr type)]{

Annotates @racket[expr] with @racket[type]. If @racket[expr] does not have the given type, a type
error is produced.

@(hackett-examples
  (: 42 Integer)
  (: "hello" String)
  (eval:error (: "hello" Integer)))

Additionally, some forms (such as @racket[def] and @racket[defn]) recognize literal uses of @racket[:]
to provide additional locations for type annotations.}

@subsection[#:tag "reference-definitions"]{Definitions}

@defform[#:literals [:]
         (def id maybe-type val-expr)
         #:grammar
         ([maybe-type (code:line : type)
                      (code:line)])]{

Hackett’s basic definition form. Defines a new binding named @racket[id] with the value
@racket[val-expr]. If @racket[type] is provided, it is used as the type for @racket[id], and
@racket[val-expr]’s type is checked against the annotation. Otherwise, a type for @racket[id] is
inferred from @racket[val-expr].

@(hackett-examples
  (def x 7)
  (eval:check x 7)
  (def y : Integer 7)
  (eval:error (def z : String 7)))}

@defform[#:literals [:]
         (defn id maybe-type
           [[arg-pat ...+] body-expr] ...+)
         #:grammar
         ([maybe-type (code:line : type)
                      (code:line)])]{

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
    [[x] (* x x)])
  (eval:check (square 5) 25))}

@subsection[#:tag "reference-anonymous-functions"]{Anonymous Functions}

@deftogether[
 [@defform[(lambda [arg-pat ...+] body-expr)]
  @defform[(λ [arg-pat ...+] body-expr)]]]{

Produces a @tech{curried} function. The curried arity of the produced function will be the same as the
number of @racket[arg-pat]s provided. When the function is applied, the provided arguments will be
matched against each @racket[arg-pat], and the function’s result will be @racket[body-expr].

@(hackett-examples
  (eval:check ((λ [x y] (+ x (* y 2))) 5 10) 25))}

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

@(define data-examples-eval
   (make-hackett-eval
    '[(data Foo
            (foo1 Integer Bool)
            (foo2 String)
            foo3)]))
@defform[(data type-clause data-clause ...)
         #:grammar
         ([type-clause type-id
                       (type-constructor-id param-id ...+)]
          [data-clause value-id
                       (data-constructor-id arg-type ...+)])]{

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
  (eval:alts
   (eval:no-prompt
    (data Foo
      (foo1 Integer Bool)
      (foo2 String)
      foo3))
   (code:line))
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
    [foo3       3]))}
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

@subsection[#:tag "reference-unit"]{Unit}

@defdata[Unit unit]{

The unit type. Values of type @racket[Unit] only have one possible value (ignoring @tech{bottom}),
@racket[unit]. A value of type @racket[unit] carries no information, so it is similar to @void-const
in @hash-lang[] @racketmodname[racket] or the @tt{void} return “type” in many C-like languages.}

@subsection[#:tag "reference-booleans"]{Booleans}

@defdata[Bool true false]{

The boolean type, representing two binary states.}

@defthing[not {Boolean -> Boolean}]{

Inverts the value it is applied to; this is, produces @racket[false] when given @racket[true] and
produces @racket[true] when given @racket[false].}

@subsection[#:tag "reference-optionals"]{Optionals}

@defdata[(Maybe a) (just a) nothing]{

A type that encodes the notion of an optional or nullable value. A value of type @racket[(Maybe a)]
implies that it @emph{might} contain a value of type @racket[a], but it also might contain nothing at
all. This type is usually used to represent operations that can fail (where @racket[nothing]
represents failure) or values that are not required to be present.}
