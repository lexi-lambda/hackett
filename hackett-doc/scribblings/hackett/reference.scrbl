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

@subsection[#:tag "reference-local-binding"]{Local Bindings}

@defform[#:literals [:]
         (let ([id maybe-type val-expr] ...+)
           body-expr)
         #:grammar
         ([maybe-type (code:line : type)
                      (code:line)])]{

Defines @emph{local} bindings, bindings which are only available within the syntactic extent of the
@racket[let] block. Each @racket[id] is bound to the result of @racket[val-expr], from top to bottom.
Each @racket[id] is in scope in @emph{subsequent} @racket[val-expr]s, and all @racket[id]s are in
scope in @racket[body-expr] (unless shadowed by another binding).

@(hackett-examples
  (eval:check (let ([x 10])
                x)
              10)
  (eval:check (let ([x 10]
                    [y (+ x 1)])
                y)
              11)
  (eval:check (let ([x 10]
                    [y {x + 1}]
                    [z {y * 2}])
                z)
              22))}

@defform[#:literals [:]
         (letrec ([id maybe-type val-expr] ...+)
           body-expr)
         #:grammar
         ([maybe-type (code:line : type)
                      (code:line)])]{

Like @racket[let], but the bindings created are potentially mutually-recursive. Each @racket[id] is
bound to the result of @racket[val-expr], and each @racket[id] is in scope within each
@racket[val-expr] as well as the @racket[body-expr]. Unlike @racket[let], all @racket[id]s must be
unique.

This allows @racket[val-expr]s to refer to themselves (to create circular values or recursive
functions) or other bindings (to create shared or mututally recursive values or functions).

@(hackett-examples
  (letrec ([xs {1 :: xs}])
    (take 5 xs))
  (letrec ([xs {1 :: ys}]
           [ys {2 :: xs}])
    (take 5 xs)))}

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

@defthing[|.| (forall [a b c] {{b -> c} -> {a -> b} -> {a -> c}})]{

Function composition. Given two functions @racket[_f] and @racket[_g], then @racket[({_f |.| _g} _x)]
is equivalent to @racket[(_f (_g _x))].

@(hackett-examples
  (def add1AndDouble {(* 2) |.| (+ 1)})
  (eval:check (add1AndDouble 3) 8))}

@defthing[$ (forall [a b] {{a -> b} -> a -> b})]{

Function application as a binary operator. Not especially useful, since @racket[{_f $ _x}] is
equivalent to @racket[(_f _x)], but sometimes convenient when used higher-order.}

@defthing[& (forall [a b] {a -> {a -> b} -> b})]{

Reverse function application. This function is a flipped version of @racket[$] that accepts the
argument first and the function second.}

@defthing[flip (forall [a b c] {{a -> b -> c} -> b -> a -> c})]{

Produces a function with the same behavior as another function, but with its first two arguments
flipped.

@(hackett-examples
  (flip :: nil 3))}

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

@defthing[head (forall [a] {(List a) -> (Maybe a)})]{

Returns @racket[just] the first element of a list, or @racket[nothing] if the list is @racket[nil].

@(hackett-examples
  (head {1 :: 2 :: 3 :: nil})
  (head (: nil (List Integer))))}

@defthing[tail (forall [a] {(List a) -> (Maybe (List a))})]{

Returns @racket[just] a list without its first element, or @racket[nothing] if the list is
@racket[nil].

@(hackett-examples
  (tail {1 :: 2 :: 3 :: nil})
  (tail (: nil (List Integer))))}

@defproc[(take [n Integer] [xs (List a)]) (List a)]{

Produces a list with the first @racket[n] elements of @racket[xs]. If @racket[xs] contains fewer than
@racket[n] elements, @racket[xs] is returned unmodified.

@(hackett-examples
  (take 2 {1 :: 2 :: 3 :: nil})
  (take 2 {1 :: nil}))}

@section[#:tag "reference-typeclasses"]{Typeclasses}

@subsection[#:tag "reference-defining-typeclasses"]{Defining typeclasses and typeclass instances}

@defform[#:literals [: =>]
         (class maybe-superclasses (class-id var-id)
           [method-id : method-type] ...)
         #:grammar
         ([maybe-superclasses (code:line superclass-constraint ... =>)
                              (code:line)])]{

Defines a @deftech{typeclass}. As the name implies, a typeclass describes a @italic{class}, or set, of
@tech{types}. Types that belong to the class are known as @tech[#:key "typeclass instance"]{instances}
or @italic{members} of the class, which are defined using the associated @racket[instance] form.

A typeclass defines a set of @deftech{typeclass methods}, each named @racket[method-id], which are
operations that must be implemented by all members of the class. Implementations of typeclass methods
must match the provided @racket[method-type], with the @racket[var-id] replaced by the type the
instance is being defined for.}

@defform[#:literals [forall =>]
         (instance instance-spec
           [method-id method-expr] ...)
         #:grammar
         ([instance-spec (class-id instance-type)
                         (forall [var-id ...] maybe-constraints
                                 (class-id instance-type))]
          [maybe-constraints (code:line instance-constraint ... =>)
                             (code:line)])]{

Defines a @deftech{typeclass instance}, which declares that the given @racket[instance-type] belongs
to the @tech{typeclass} bound to @racket[class-id].}

@subsection[#:tag "reference-show"]{Printing for debugging}

@defclass[(Show a)
          [show {a -> String}]]{

A class for converting values to @racket[String] representations for the purposes of debugging.
Generally, the @racket[Show] instance for a type should produce a valid Hackett expression that, when
evaluated, produces the value.

@defmethod[show {a -> String}]{

@(hackett-examples
  (show 42)
  (show "hello")
  (show (just 11))
  (show {1 :: 2 :: 3 :: nil}))}}

@subsection[#:tag "reference-equality"]{Equality}

@defclass[(Eq a)
          [== {a -> a -> Bool}]]{
The class of types with a notion of equality. The @racket[==] method should produce @racket[true] if
both of its arguments are equal, otherwise it should produce @racket[false].

@defmethod[== {a -> a -> Bool}]{

@(hackett-examples
  (eval:check {10 == 10} true)
  (eval:check {10 == 11} false)
  (eval:check {{1 :: 2 :: nil} == {1 :: 2 :: nil}} true)
  (eval:check {{1 :: 2 :: nil} == {1 :: nil}} false)
  (eval:check {{1 :: 2 :: nil} == {1 :: 3 :: nil}} false))}}

@subsection[#:tag "reference-semigroup-monoid"]{Semigroups and monoids}

@defclass[(Semigroup a)
          [++ {a -> a -> a}]]{

The class of @deftech{semigroups}, types with an associative binary operation, @racket[++]. Generally,
@racket[++] defines some notion of combining or appending, as is the case with the instances for
@racket[String] and @racket[(List _a)], but this is not necessarily true.

@defmethod[++ {a -> a -> a}]{

An associative operation. That is, @racket[++] must obey the following law:

@racketblock[
  @#,racket[{{_a ++ _b} ++ _c}] @#,elem[#:style 'roman]{=} @#,racket[{_a ++ {_b ++ _c}}]]

@(hackett-examples
  {"hello" ++ ", " ++ "world!"}
  {{1 :: 2 :: nil} ++ {3 :: 4 :: nil}})}}

@defclass[#:super [(Semigroup a)]
          (Monoid a)
          [mempty a]]{

A @deftech{monoid} extends the notion of a @tech{semigroup} with the notion of an identity element,
@racket[mempty].

@defmethod[mempty a]{

An identity element for @racket[++]. That is, @racket[mempty] must obey the following laws:

@racketblock[
  @#,racket[{_a ++ mempty}] @#,elem[#:style 'roman]{=} @#,racket[_a]
  @#,racket[{mempty ++ _a}] @#,elem[#:style 'roman]{=} @#,racket[_a]]

@(hackett-examples
  (: mempty String)
  (: mempty (List Integer)))}}

@subsection[#:tag "reference-functor"]{Functors}

@defclass[(Functor f)
          [map (forall [a b] {{a -> b} -> (f a) -> (f b)})]]{

A class of types that are @deftech{functors}, essentially types that provide a mapping or “piercing”
operation. The @racket[map] function can be viewed in different ways:

  @itemlist[
    @item{The @racket[map] function can be thought of as applying a function to each “element” of some
          “container”. This metaphor applies to many members of the @racket[Functor] typeclass, such
          as @racket[List] and @racket[Maybe], but does not apply well to all of them.}

    @item{More generally, @racket[map] can be viewed as a “lifting” operation, which “lifts” a
          function of type @racket[{_a -> _b}] to a function of type @racket[{(f _a) -> (f _b)}] for
          some type @racket[f]. This is a very general notion, and the meaning of such an operation is
          highly dependent on the particular choice of @racket[f].}]

All @racket[map] implementations must obey the following laws:

@racketblock[
  @#,racket[(map id)] @#,elem[#:style 'roman]{=} @#,racket[id]
  @#,racket[(map {_f |.| _g}) @#,elem[#:style 'roman]{=} @#,racket[{(map _f) |.| (map _g)}]]]

@defmethod[map (forall [a b] {{a -> b} -> (f a) -> (f b)})]{

@(hackett-examples
  (map (+ 1) {1 :: 2 :: nil})
  (map (+ 1) (just 10))
  (map (+ 1) nothing))}}

@defthing[<$> (forall [f a b] (Functor f) => {{a -> b} -> (f a) -> (f b)})]{

An alias for @racket[map], intended to be used in @tech{infix mode} instead of prefix, especially when
mixed with @racket[<*>] in the same expression.

@(hackett-examples
  {(+ 1) <$> {1 :: 2 :: nil}}
  {(+ 1) <$> (just 10)}
  {(+ 1) <$> nothing})}

@defthing[<&> (forall [f a b] (Functor f) => {(f a) -> {a -> b} -> (f b)})]{

A flipped version of @racket[<$>] for when it’s preferable to take the function argument second, like
@racket[&] but lifted to a @tech{functor}.}

@defthing[<$ (forall [f a b] (Functor f) => {b -> (f a) -> (f b)})]{

Equivalent to @racket[{map |.| const}]. Replaces all values of type @racket[_a] with a new value of
type @racket[_b].

@(hackett-examples
  {10 <$ (just 1)}
  {10 <$ {1 :: 2 :: 3 :: nil}})}

@defthing[$> (forall [f a b] (Functor f) => {(f a) -> b -> (f b)})]{

A flipped version of @racket[<$].}

@defthing[ignore (forall [f a] (Functor f) => {(f a) -> (f Unit)})]{

Replaces the result of a @tech{functor} with @racket[unit]. Equivalent to @racket[(<$ unit)].}

@subsection[#:tag "reference-applicative"]{Applicative functors}

@defclass[#:super [(Functor f)]
          (Applicative f)
          [pure (forall [a] {a -> (f a)})]
          [<*> (forall [a b] {(f {a -> b}) -> (f a) -> (f b)})]]{

The class of @deftech{applicative functors}, which are @tech{functors} with some notion of
application, @racket[<*>]. Additionally, applicative functors must provided a lifting operation,
@racket[pure], which embeds any value into @racket[f].

Applicative functors must satisfy the following laws:

@racketblock[
  @#,racket[{(pure id) <*> _v}] @#,elem[#:style 'roman]{=} @#,racket[_v]
  @#,racket[{(pure |.|) <*> _u <*> _v <*> _w}] @#,elem[#:style 'roman]{=} @#,racket[{_u <*> (_v <*> _w)}]
  @#,racket[{(pure _f) <*> (pure _x)}] @#,elem[#:style 'roman]{=} @#,racket[(pure (_f _x))]
  @#,racket[{_u <*> (pure _y)}] @#,elem[#:style 'roman]{=} @#,racket[{(pure (& _y) <*> _u)}]]

As a consequence of these laws, the @racket[Functor] instance for @racket[f] will satisfy:

@racketblock[
  @#,racket[(map _f _x)] @#,elem[#:style 'roman]{=} @#,racket[{(pure _f) <*> _x}]]

@defmethod[pure (forall [a] {a -> (f a)})]{

Lifts a value.

@(hackett-examples
  (: (pure 11) (Maybe Integer))
  (: (pure 11) (List Integer)))}

@defmethod[<*> (forall [a b] {(f {a -> b}) -> (f a) -> (f b)})]{

Applies a function in a context. While @racket[map]/@racket[<$>] “lifts” a pure function to a function
that operates on a functor, @racket[<*>] applies a function that is already inside the context of a
@tech{functor}.

@(hackett-examples
  {(just not) <*> (just true)}
  {(just not) <*> (just false)}
  {(just not) <*> nothing}
  {(: nothing (Maybe {Bool -> Bool})) <*> (just true)})

Due to currying, this is especially useful in combination with @racket[<$>] to apply a multi-argument
function to multiple arguments within the context of some functor. For example, @racket[Maybe]
implements a sort of short-circuiting, where any @racket[nothing] will cause the entire computation to
produce @racket[nothing].

@(hackett-examples
  {+ <$> (just 1) <*> (just 2)}
  {+ <$> nothing <*> (just 2)}
  {+ <$> (just 1) <*> nothing})

This works because @racket[{_f <$> _x}] is guaranteed to be equivalent to @racket[{(pure _f) <*> _x}]
by the applicative laws, and since functions are curried, each use of @racket[<*>] applies a single
argument to the (potentially partially-applied) function.}}

@defthing[sequence (forall [f a] (Applicative f) => {(List (f a)) -> (f (List a))})]{

Produces an action that runs a @tech{list} of @tech[#:key "applicative functor"]{applicative} actions
from left to right, then collects the results into a new list.

@(hackett-examples
  (sequence {(just 1) :: (just 2) :: (just 3) :: nil})
  (sequence {(just 1) :: nothing :: (just 3) :: nil}))}

@defthing[traverse (forall [f a b] (Applicative f) => {{a -> (f b)} -> (List a) -> (f (List b))})]{

Applies a function to each element of a @tech{list} to produce an @tech[#:key "applicative functor"]{
applicative} action, then collects them left to right @italic{a la} @racket[sequence]
(@racket[(traverse _f _xs)] is equivalent to @racket[(sequence (map _f _xs))]).

@(hackett-examples
  (traverse head {{1 :: nil} :: {2 :: 3 :: nil} :: nil})
  (traverse head {{1 :: nil} :: nil :: nil}))}

@subsection[#:tag "reference-monad"]{Monads}

@defclass[#:super [(Applicative m)]
          (Monad m)
          [join (forall [a] {(m (m a)) -> (m a)})]]{

The class of @deftech{monads}, which are @tech{applicative functors} augmented with a single
@racket[join] operation that allows multiple “layers” of @racket[m] to be “flattened” into a single
one. Like @tech{functors} and @tech{applicative functors}, monads are a highly abstract concept, but
they can be most usefully thought of as an abstraction notion of sequential actions.

Monads must satisfy the following laws:

@racketblock[
  @#,racket[{join |.| pure}] @#,elem[#:style 'roman]{=} @#,racket[id]
  @#,racket[{join |.| (map pure)}] @#,elem[#:style 'roman]{=} @#,racket[id]
  @#,racket[{join |.| join}] @#,elem[#:style 'roman]{=} @#,racket[{join |.| (map join)}]]

Generally, it is more useful to use @racket[=<<] or @racket[do] than to use @racket[join] directly.

@defmethod[join (forall [a] {(m (m a)) -> (m a)})]{

@(hackett-examples
  (join (just (just 3)))
  (join (just (: nothing (Maybe Integer))))
  (join (: nothing (Maybe (Maybe Integer))))
  (join {{1 :: nil} :: {2 :: 3 :: nil} :: nil}))}}

@defthing[=<< (forall [m a b] (Monad m) => {{a -> (m b)} -> (m a) -> (m b)})]{

Applies a function that produces a @tech[#:key "monad"]{monadic} value to a monadic value. The
expression @racket[{_f =<< _x}] is equivalent to @racket[(join {_f <$> _x})]. It is worth comparing
and contrasting the types of @racket[map]/@racket[<$>], @racket[<*>], and @racket[=<<], all of which
are similar but slightly different.

@(hackett-examples
  {head =<< (tail {1 :: 2 :: nil})}
  {head =<< (tail {1 :: nil})}
  {head =<< (tail (: nil (List Integer)))})}

@defthing[>>= (forall [m a b] (Monad m) => {(m a) -> {a -> (m b)} -> (m b)})]{

A flipped version of @racket[=<<].}

@defform[#:literals [<-]
         (do do-clause ... monadic-expr)
         #:grammar
         ([do-clause [binding-id <- monadic-expr]
                     monadic-expr])]{

A convenient, imperative-style shorthand for a sequence of monadic expressions chained together with
@racket[>>=]. Each @racket[do-clause] corresponds to a single use of @racket[>>=], and each
@racket[monadic-expr] must have a type with the shape @racket[(_m _a)], where @racket[_m] is a
@racket[Monad].

Any use of @racket[do] with a single subform expands to the subform: @racket[(do _expr)] is equivalent
to @racket[_expr]. Each @racket[do-clause] introduces a use of @racket[>>=], with the result
potentially bound to a @racket[binding-id]. That is, @racket[(do [_x <- _m] _more ...+)] expands to
@racket[{_ma >>= (λ [_x] (do _more ...))}], and @racket[(do _m _more ...+)] expands to
@racket[{_ma >>= (λ [_] (do _more ...))}].

This is often much more readable than writing the uses of @racket[>>=] out by hand, especially when
the result of each action must be give a name.

@(hackett-examples
  (do [xs <- (tail {1 :: 2 :: 3 :: 4 :: nil})]
      [ys <- (tail xs)]
      [zs <- (tail ys)]
      (head zs))
  (do [xs <- (tail {1 :: 2 :: 3 :: nil})]
      [ys <- (tail xs)]
      [zs <- (tail ys)]
      (head zs)))}

@defthing[ap (forall [m a b] (Monad m) => {(m {a -> b}) -> (m a) -> (m b)})]{

An implementation of @racket[<*>] in terms of @racket[map], @racket[pure], and @racket[join]. This can
be used as an implementation of @racket[<*>] as long as @racket[join] does not use @racket[<*>] (if it
does, the two will likely infinitely mutually recur).}

@section[#:tag "reference-controlling-evaluation"]{Controlling Evaluation}

@defthing[seq (forall [a b] {a -> b -> b})]{

Accepts two arguments and returns its second argument. When the result is forced, the first argument
will also be evaluated to weak head normal form. This can be used to reduce laziness.}

@defthing[error! (forall [a] {String -> a})]{

@see-guide-note["guide-bottoms"]{partial functions}

A simple @tech{partial function} that crashes the program with a message when evaluated.}

@defthing[undefined! (forall [a] a)]{

A @tech[#:key "partial function"]{partial} value that crashes the program when evaluated.}
