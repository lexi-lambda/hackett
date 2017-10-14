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
  (instance (Show Foo)
    [show (λ* [[(foo1 a b)] {"(foo1 " ++ (show a) ++ " "
                                      ++ (show b) ++ ")"}]
              [[(foo2 a)] {"(foo2 " ++ (show a) ++ ")"}]
              [[foo3] "foo3"])])
  (#:type foo1)
  (foo1 42 true)
  (#:type foo2)
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
  (instance (forall [a] (Show a) => (Show (Tree a)))
    [show (λ* [[{a :&: b}] {"{" ++ (show a) ++ " :&: " ++ (show b) ++ "}"}]
              [[(leaf a)] {"(leaf " ++ (show a) ++ ")"}])])
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

@deftogether[
 [@defthing[> {Integer -> Integer -> Bool}]
  @defthing[< {Integer -> Integer -> Bool}]
  @defthing[>= {Integer -> Integer -> Bool}]
  @defthing[<= {Integer -> Integer -> Bool}]]]{

Comparison operators on integers.}

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

@defthing[string-length {String -> Integer}]{

Returns the length of a string, in characters.

@(hackett-examples
  (eval:check (string-length "hello") 5)
  (eval:check (string-length "Λάμβδα") 6))}

@defthing[string-split {String -> String -> (List String)}]{

Splits a string on all instances of a separator string.

@(hackett-examples
  (string-split "," "1,2,3,4,5")
  (string-split "," ",2,,4,")
  (string-split "," ",,,,"))}

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

The @deftech{boolean} type, representing two binary states.}

@defthing[not {Bool -> Bool}]{

Inverts the @tech{boolean} it is applied to; that is, produces @racket[false] when given @racket[true]
and produces @racket[true] when given @racket[false].}

@defthing[if (forall [a] {Bool -> a -> a -> a})]{

Performs case analysis on a @tech{boolean} value. If the supplied boolean is @racket[true], returns
its second argument; otherwise, returns its third argument.

Since Hackett is lazy, @racket[if] is an ordinary function, not a macro or special form, and it can be
used higher-order if desired.

@(hackett-examples
  (eval:check (if true "first" "second") "first")
  (eval:check (if false "first" "second") "second"))}

@defthing[\|\| {Bool -> Bool -> Bool}]{

Returns @racket[true] if its first argument is @racket[true]; otherwise, returns its second argument.
Notably, the second argument will not be evaluated at all if the first argument is @racket[true], but
the first argument will always be forced when the result is forced.

@(hackett-examples
  (eval:check {true \|\| true} true)
  (eval:check {false \|\| true} true)
  (eval:check {true \|\| false} true)
  (eval:check {false \|\| false} false)
  (eval:check {true \|\| (error! "never gets here")} true))}

@defthing[&& {Bool -> Bool -> Bool}]{

Returns @racket[false] if its first argument is @racket[false]; otherwise, returns its second
argument. Notably, the second argument will not be evaluated at all if the first argument is
@racket[false], but the first argument will always be forced when the result is forced.

@(hackett-examples
  (eval:check {true && true} true)
  (eval:check {false && true} false)
  (eval:check {true && false} false)
  (eval:check {false && false} false)
  (eval:check {false && (error! "never gets here")} false))}

@subsection[#:tag "reference-identity"]{The Identity Type}

@defmodule[hackett/data/identity]

@defdata[(Identity a) (identity a)]{

A simple wrapper type with a variety of typeclass instances that defer to the value inside whenever
possible. Most useful for its @racket[Functor], @racket[Applicative], and @racket[Monad] instances,
which simply apply functions to the value inside the @racket[identity] wrapper, making it serve as
a “no-op” wrapper of sorts.

@(hackett-interaction
  (identity 5)
  (map (+ 1) (identity 5))
  {(identity (+ 1)) <*> (identity 5)}
  {(identity "hello, ") ++ (identity "world")})}

@defproc[(run-identity [x (Identity a)]) a]{

Unwraps and returns the value inside an @racket[identity] wrapper.

@(hackett-interaction
  (run-identity (identity 5)))}

@subsection[#:tag "reference-tuples"]{Tuples}

@defdata[(Tuple a b) (tuple a b)]{

The @deftech{tuple} type, which contains a pair of possibly heterogenous values.}

@defthing[fst (forall [a b] {(Tuple a b) -> a})]{

Extracts the first element of a @tech{tuple}.

@(hackett-examples
  (eval:check (fst (tuple 42 "hello")) 42))}

@defthing[snd (forall [a b] {(Tuple a b) -> b})]{

Extracts the second element of a @tech{tuple}.

@(hackett-examples
  (eval:check (snd (tuple 42 "hello")) "hello"))}

@subsection[#:tag "reference-optionals"]{Optionals}

@defdata[(Maybe a) (just a) nothing]{

A type that encodes the notion of an optional or nullable value. A value of type @racket[(Maybe a)]
implies that it @emph{might} contain a value of type @racket[a], but it also might contain nothing at
all. This type is usually used to represent operations that can fail (where @racket[nothing]
represents failure) or values that are not required to be present.

@(hackett-examples
  (map (+ 1) (just 5))
  (map (+ 1) nothing))}

@defproc[(maybe [v b] [f {a -> b}] [x (Maybe a)]) b]{

The catamorphism for @racket[Maybe]. Produces @racket[v] when @racket[x] is @racket[nothing] and
produces @racket[(f _y)] when @racket[x] is @racket[(just _y)].

@(hackett-examples
  (eval:check (maybe 0 (+ 1) (just 5)) 6)
  (eval:check (maybe 0 (+ 1) nothing) 0))}

@defproc[(from-maybe [v a] [x (Maybe a)]) a]{

Extracts the value inside @racket[x], producing a default value @racket[v] when @racket[x] is
@racket[nothing]. Equivalent to @racket[(maybe v id)].

@(hackett-examples
  (eval:check (from-maybe 0 (just 5)) 5)
  (eval:check (from-maybe 0 nothing) 0))}

@defdata[(Either a b) (left a) (right b)]{

A type that encodes the notion of a successful result or an error. The @racket[Functor],
@racket[Applicative], and @racket[Monad] instances for @racket[(Either a)] are “right-biased”, so they
will short-circuit on values wrapped in @racket[left] and will perform mapping or sequencing on values
wrapped in @racket[right].

This type is generally used in a similar way to @racket[Maybe], but it allows the sort of failure to
be explicitly tagged, usually returning a error message or failure reason on the @racket[left] side.

@(hackett-examples
  (map (+ 1) (: (right 5) (Either String Integer)))
  (map (+ 1) (: (left "an error happened") (Either String Integer))))}

@defproc[(either [f {a -> c}] [g {b -> c}] [x (Either a b)]) c]{

The catamorphism for @racket[Either]. Produces @racket[(f _y)] when @racket[x] is @racket[(left _y)]
and produces @racket[(g _z)] when @racket[x] is @racket[(right _z)].

@(hackett-examples
  (eval:check (either (+ 1) (* 2) (left 5)) 6)
  (eval:check (either (+ 1) (* 2) (right 5)) 10))}

@defproc[(is-left [e (Either a b)]) Bool]{

This predicate is @racket[true] when @racket[e] is of the form @racket[(left x)] for some @racket[x],
and is false when @racket[e] is @racket[(right x)].

@(hackett-examples
  (eval:check (is-left (left "nifty")) true)
  (eval:check (is-left (right "tubular")) false))}

@defproc[(is-right [e (Either a b)]) Bool]{

This predicate is @racket[true] when @racket[e] is of the form @racket[(right x)] for some @racket[x],
and is false when @racket[e] is @racket[(left x)].

@(hackett-examples
  (eval:check (is-right (left "nifty")) false)
  (eval:check (is-right (right "tubular")) true))}

@defproc[(lefts [es (List (Either a b))]) (List a)]{

Extract all values of the form @racket[(left x)] from es.

@(hackett-examples
  (lefts {(left 1) :: (right "haskell") :: (right "racket") :: (left -32) :: nil}))}

@defproc[(rights [es (List (Either a b))]) (List b)]{

Extract all values of the form @racket[(right x)] from es.

@(hackett-examples
  (rights {(left 1) :: (right "haskell") :: (right "racket") :: (left -32) :: nil}))}

@defproc[(partition-eithers [es (List (Either a b))]) (Tuple (List a) (List b))]{

Extract every @racket[(left x)] to the first element of the pair and each @racket[(right x)] to the
second. @racket[(partition-eithers es)] is equivalent to @racket[(tuple (lefts es) (rights es))]

@(hackett-examples
  (partition-eithers {(left 1) :: (right "haskell") :: (right "racket") :: (left -32) :: nil}))}

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

@defthing[head! (forall [a] {(List a) -> a})]{

A @tech[#:key "partial function"]{partial} version of @racket[head] that returns the first element of
a list. If the list is empty, it raises an error.

@(hackett-examples
  (head! {1 :: 2 :: 3 :: nil})
  (eval:error (head! (: nil (List Integer)))))}

@defthing[tail! (forall [a] {(List a) -> (List a)})]{

A @tech[#:key "partial function"]{partial} version of @racket[tail] that returns a list without its
first element. If the list is empty, it raises an error.

@(hackett-examples
  (tail! {1 :: 2 :: 3 :: nil})
  (eval:error (tail! (: nil (List Integer)))))}

@defproc[(take [n Integer] [xs (List a)]) (List a)]{

Produces a list with the first @racket[n] elements of @racket[xs]. If @racket[xs] contains fewer than
@racket[n] elements, @racket[xs] is returned unmodified.

@(hackett-examples
  (take 2 {1 :: 2 :: 3 :: nil})
  (take 2 {1 :: nil}))}

@defproc[(drop [n Integer] [xs (List a)]) (List a)]{

Produces a list like @racket[xs] without its first @racket[n] elements. If @racket[xs] contains fewer
then @racket[n] elements, the result is @racket[nil].

@(hackett-examples
  (drop 2 {1 :: 2 :: 3 :: nil})
  (drop 2 {1 :: nil}))}

@defproc[(filter [f {a -> Bool}] [xs (List a)]) (List a)]{

Produces a list that contains each element, @racket[_x], for which @racket[_x] is an element of
@racket[xs] and @racket[(f _x)] is @racket[true].

@(hackett-examples
  (filter (λ [x] {x > 5}) {3 :: 7 :: 2 :: 9 :: 12 :: 4 :: nil}))}

@defproc[(foldr [f {a -> b -> b}] [acc b] [xs (List a)]) b]{

Reduces @racket[xs] to a single value using a right-associative binary operator, @racket[f], using
@racket[acc] as a “seed” element. Uses of @racket[foldr] can be thought of as a series of nested,
right-associative applications of @racket[f], so if @racket[xs] contains elements named @racket[_x0],
@racket[_x1], @racket[_x2] etc., up to @racket[_xn], then @racket[(foldr f acc xs)] is equivalent to
the following expression:

@(racketblock
  {_x0 f {_x1 f {_x2 f .... {_xn f acc} ....}}})

@(hackett-examples
  (foldr + 0 {1 :: 2 :: 3 :: 4 :: 5 :: nil})
  (foldr * 1 {1 :: 2 :: 3 :: 4 :: 5 :: nil})
  (foldr - 0 {1 :: 2 :: 3 :: 4 :: 5 :: nil})
  (foldr :: nil {1 :: 2 :: 3 :: 4 :: 5 :: nil}))}

@defproc[(foldl [f {b -> a -> b}] [acc b] [xs (List a)]) b]{

Reduces @racket[xs] to a single value using a left-associative binary operator, @racket[f], using
@racket[acc] as a “seed” element. Uses of @racket[foldr] can be thought of as a series of nested,
left-associative applications of @racket[f], so if @racket[xs] contains elements named @racket[_x0],
@racket[_x1], @racket[_x2] etc., up to @racket[_xn], then @racket[(foldr f acc xs)] is equivalent to
the following expression:

@(racketblock
  {.... {{{acc f _x0} f _x1} f _x2} .... _xn})

@(hackett-examples
  (foldl + 0 {1 :: 2 :: 3 :: 4 :: 5 :: nil})
  (foldl * 1 {1 :: 2 :: 3 :: 4 :: 5 :: nil})
  (foldl - 0 {1 :: 2 :: 3 :: 4 :: 5 :: nil}))}

@defproc[(sum [xs (List Integer)]) Integer]{

Adds the elements of @racket[xs] together and returns the sum. Equivalent to @racket[(foldl + 0)].

@(hackett-examples
  (eval:check (sum {1 :: 2 :: 3 :: nil}) 6)
  (eval:check (sum nil) 0))}

@section[#:tag "reference-typeclasses"]{Typeclasses}

@subsection[#:tag "reference-defining-typeclasses"]{Defining typeclasses and typeclass instances}

@defform[#:literals [: =>]
         (class maybe-superclasses (class-id var-id ...)
           [method-id : method-type maybe-default-method-impl] ...)
         #:grammar
         ([maybe-superclasses (code:line superclass-constraint ... =>)
                              (code:line)]
          [maybe-default-method-impl default-method-impl-expr
                                     (code:line)])]{

Defines a @deftech{typeclass}. As the name implies, a typeclass describes a @italic{class}, or set, of
@tech{types}. Types that belong to the class are known as @tech[#:key "typeclass instance"]{instances}
or @italic{members} of the class, which are defined using the associated @racket[instance] form.

A typeclass defines a set of @deftech{typeclass methods}, each named @racket[method-id], which are
operations that must be implemented by all members of the class. Implementations of typeclass methods
must match the provided @racket[method-type], with the @racket[var-id]s replaced by the types the
instance is being defined for.

For each @racket[method-id], a @deftech{default method} may be provided as
@racket[default-method-impl-expr], which will be used if any instance opts to not specify an explicit
implementation for that method. Each default method implementation must be polymorphic enough to be a
valid implementation for any instance of the class. Default methods are generally used when a
typeclass method may be defined in terms of other typeclass methods, but the implementor can be given
a choice of which methods to implement, or they can provide a more efficient implementation for
commonly-used methods.}

@defform[#:literals [forall =>]
         (instance instance-spec
           [method-id method-expr] ...)
         #:grammar
         ([instance-spec (class-id instance-type ...)
                         (forall [var-id ...] maybe-constraints
                                 (class-id instance-type ...))]
          [maybe-constraints (code:line instance-constraint ... =>)
                             (code:line)])]{

Defines a @deftech{typeclass instance}, which declares that the given @racket[instance-type]s belong
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

A class of types that are @deftech{functors}, essentially types that provide a mapping or “lifting”
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
          [join (forall [a] {(m (m a)) -> (m a)})]
          [=<< (forall [a b] {{a -> (m b)} -> (m a) -> (m b)})]]{

The class of @deftech{monads}, which are @tech{applicative functors} augmented with a single
@racket[join] operation that allows multiple “layers” of @racket[m] to be “flattened” into a single
one. Like @tech{functors} and @tech{applicative functors}, monads are a highly abstract concept, but
they can be most usefully thought of as an abstraction notion of sequential actions.

Monads must satisfy the following laws:

@racketblock[
  @#,racket[{join |.| pure}] @#,elem[#:style 'roman]{=} @#,racket[id]
  @#,racket[{join |.| (map pure)}] @#,elem[#:style 'roman]{=} @#,racket[id]
  @#,racket[{join |.| join}] @#,elem[#:style 'roman]{=} @#,racket[{join |.| (map join)}]]

The @racket[=<<] operation is pronounced “bind”, and it is equivalent in power to @racket[join]. While
@racket[join] is closer to the essence of what a monad is, @racket[=<<] (or its flipped version,
@racket[>>=]) is more frequently used in ordinary programming. Either may be implemented, and a
default implementation will be provided for the other, or an implementation may be provided for both
if a more efficient implementation can be provided.

It is often more useful to use @racket[do] than to use @racket[join] or @racket[=<<] directly.

@defmethod[join (forall [a] {(m (m a)) -> (m a)})]{

@(hackett-examples
  (join (just (just 3)))
  (join (just (: nothing (Maybe Integer))))
  (join (: nothing (Maybe (Maybe Integer))))
  (join {{1 :: nil} :: {2 :: 3 :: nil} :: nil}))}

@defmethod[=<< (forall [a b] {{a -> (m b)} -> (m a) -> (m b)})]{

Applies a function that produces a monadic value to a monadic value. The expression
@racket[{_f =<< _x}] is equivalent to @racket[(join {_f <$> _x})] (and an explicit implementation of
both methods must maintain that law). It is worth comparing and contrasting the types of
@racket[map]/@racket[<$>], @racket[<*>], and @racket[=<<], all of which are similar but slightly
different.

@(hackett-examples
  {head =<< (tail {1 :: 2 :: nil})}
  {head =<< (tail {1 :: nil})}
  {head =<< (tail (: nil (List Integer)))})}}

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

@section[#:tag "reference-io"]{I/O}

@defform[#:kind "type constructor" (IO a)]{

The type of @deftech{I/O actions}, which are @tech{monads}. Hackett’s encoding of I/O is semantically
pure—evaluating an I/O action does not cause any side-effects to be performed. The only way to
“execute” an I/O action is to provide it to the @racket[main] form, which instructs the Hackett
runtime to perform the actual I/O actions described by the @racket[IO] value.

It may be helpful to think of a value of type @racket[(IO a)] as a set of @emph{instructions} to
obtain a value of type @racket[a]. This makes it clear that it is @bold{impossible} to get the value
“inside” an @racket[IO] action, since no such value exists; there is no @racket[String] “inside” a
value of type @racket[(IO String)].

Since @racket[main] is the only way to ask the runtime to execute the instructions contained within
an @racket[IO] action, and @racket[main] is only legal at the top level of a module, it is impossible
for I/O to be performed locally. This is how Hackett preserves referential transparency @emph{even
within} functions that produce values of type @racket[IO].}

@defform[(main action)
         #:contracts
         ([action (IO _a)])]{

Appends an @tech{I/O action} to the current module’s @deftech{main actions}. Main actions are executed
by the runtime whenever a module is run directly, e.g. from DrRacket or via the @tt{racket}
executable, rather than imported via @racket[require]. This form is only legal at the top level of a
module.

Uses of this form correspond to definitions of @racketid[main] submodules in @hash-lang[]
@racketmodname[racket]. For more information, see
@secref["main-and-test" #:doc '(lib "scribblings/guide/guide.scrbl")].}

@defproc[(print [str String]) (IO Unit)]{

Produces an @tech{I/O action} that prints @racket[str] to standard output.}

@defproc[(println [str String]) (IO Unit)]{

Like @racket[print], but appends a newline to the end of the printed message.}

@section[#:tag "reference-monad-transformers"]{Monad Transformers}

@defmodule[hackett/monad/trans]

@defclass[(MonadTrans t)
          [lift (forall [m a] {(m a) -> (t m a)})]]{

The class of @deftech{monad transformers}. A monad transformer builds a new monad from an existing
one, extending it with additional functionality. In this sense, monad transformers can be thought of
as “monad mixins”.

Instances should satisfy the following laws:

@racketblock[
  @#,racket[{lift |.| pure}] @#,elem[#:style 'roman]{=} @#,racket[pure]
  @#,racket[(lift {_m >>= _f})] @#,elem[#:style 'roman]{=} @#,racket[{(lift _m) >>= {lift |.| _f}}]]

@defmethod[lift (forall [m a] {(m a) -> (t m a)})]{

Lifts a computation from the argument monad to the constructed monad.}}

@subsection[#:tag "reference-reader-monad"]{Reader}

@defmodule[hackett/monad/reader]

@defdata[(ReaderT r m a) (reader-t {r -> (m a)})]{

The @deftech{reader monad transformer}, a @tech{monad transformer} that extends a monad with a
read-only dynamic environment. The environment can be accessed with @racket[ask] and locally modified
with @racket[local].

@(hackett-interaction
  (run-reader-t (do [x <- ask]
                    [y <- (lift {{x + 1} :: {x - 1} :: nil})]
                    (lift {{y * 2} :: {y * 3} :: nil}))
                10))}

@defproc[(run-reader-t [x (ReaderT r m a)] [ctx r]) (m a)]{

Runs the @tech{reader monad transformer} computation @racket[x] with the context @racket[ctx] and
produces a computation in the argument monad.}

@defproc[(run-reader [x (ReaderT r Identity a)] [ctx r]) a]{

Runs the @tech{reader monad transformer} computation @racket[x] with the context @racket[ctx] and
extracts the result.}

@defthing[ask (forall [r m] (ReaderT r m r))]{

A computation that fetches the value of the current dynamic environment.

@(hackett-interaction
  (eval:check (run-reader ask 5) 5)
  (eval:check (run-reader ask "hello") "hello"))}

@defproc[(asks [f {r -> a}]) (ReaderT r m a)]{

Produces a computation that fetches a value from the current dynamic environment, applies @racket[f]
to it, and returns the result.

@(hackett-interaction
  (eval:check (run-reader (asks (+ 1)) 5) 6)
  (eval:check (run-reader (asks head) {5 :: nil}) (just 5)))}

@defproc[(local [f {r -> r}] [x (ReaderT r m a)]) (ReaderT r m a)]{

Produces a computation like @racket[x], except that the environment is modified in its dynamic extent
by applying @racket[f] to it.}

@subsection[#:tag "reference-error-monad"]{Error}

@defmodule[hackett/monad/error]

@defdata[(ErrorT e m a) (error-t (m (Either e a)))]{

The @deftech{error monad transformer}, a @tech{monad transformer} that extends a monad with a notion
of failure. Failures short-circuit other computations in the monad, and they can carry information,
usually information about what caused the failure.

@(hackett-interaction
  (eval:alts (run-error-t (do (lift (println "This gets printed."))
                              (throw "Oops!")
                              (lift (println "Never gets here."))))
             (unsafe-run-io!
              (run-error-t (do (lift (println "This gets printed."))
                               (throw "Oops!")
                               (lift (println "Never gets here.")))))))}

@defproc[(run-error-t [x (ErrorT e m a)]) (m (Either e a))]{

Runs the @tech{error monad transformer} computation @racket[x] and produces the possibly-aborted
result in the argument monad.}

@defproc[(run-error [x (ErrorT e Identity a)]) (Either e a)]{

Runs the @tech{error monad transformer} computation @racket[x] and extracts the possibly-aborted
result.}

@defproc[(throw [ex e]) (ErrorT e m a)]{

Produces a computation that raises @racket[ex] as an error, aborting the current computation (unless
caught with @racket[catch]).

@(hackett-interaction
  (eval:check (: (run-error (pure 42)) (Either String Integer))
              (: (right 42) (Either String Integer)))
  (eval:check (run-error (do (throw "Ack!") (pure 42)))
              (: (left "Ack!") (Either String Integer))))}

@defproc[(catch [x (ErrorT e m a)] [handler {e -> (ErrorT e* m a)}]) (ErrorT e* m a)]{

Produces a computation like @racket[x], except any errors raised are handled via @racket[handler]
instead of immediately aborting.

@(hackett-interaction
  (eval:check (: (run-error (throw "Ack!")) (Either String String))
              (: (left "Ack!") (Either String String)))
  (eval:check (: (run-error (catch (throw "Ack!")
                              (λ [str] (pure {"Caught error: " ++ str}))))
                 (Either Unit String))
              (: (right "Caught error: Ack!") (Either Unit String))))}

@section[#:tag "reference-controlling-evaluation"]{Controlling Evaluation}

@defthing[seq (forall [a b] {a -> b -> b})]{

Accepts two arguments and returns its second argument. When the result is forced, the first argument
will also be evaluated to weak head normal form. This can be used to reduce laziness.}

@defthing[error! (forall [a] {String -> a})]{

@see-guide-note["guide-bottoms"]{partial functions}

A simple @tech{partial function} that crashes the program with a message when evaluated.}

@defthing[undefined! (forall [a] a)]{

A @tech[#:key "partial function"]{partial} value that crashes the program when evaluated.}
