#lang scribble/manual

@(require scribblings/hackett/private/util)

@(module racket-labels racket/base
   (require scribble/manual (for-label racket/base))
   (provide racket-require)
   (define racket-require @racket[require]))
@(require 'racket-labels)

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
  (: 42 t:Integer)
  (: "hello" t:String)
  (eval:error (: "hello" t:Integer)))

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
  (def y : t:Integer 7)
  (eval:error (def z : t:String 7)))

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
  (defn square : (t:-> t:Integer t:Integer)
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
  (eval:check ((λ* [[(Just x)] x]
                   [[Nothing] 0])
               (Just 42))
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
  (eval:check (case (Just 42)
                [(Just x) x]
                [Nothing 0])
              42))}

@defform[(case* [val-expr ...+]
           [[pat ...+] body-expr] ...+)]{

Like @racket[case], but matches against multiple values at once. Each case only succeeds if @emph{all}
@racket[pat]s succeed.

@(hackett-examples
  (eval:check (case* [(Just 1) (Just 2)]
                [[(Just _) Nothing] "first"]
                [[Nothing (Just _)] "second"]
                [[(Just _) (Just _)] "both"]
                [[Nothing Nothing] "neither"])
              "both"))}

@subsection[#:tag "reference-imports-exports"]{Imports}

@defform[(require require-spec ...)]{

Imports bindings from a module, just like @racket-require from @racketmodname[racket/base]. The
@racket[require] binding provided by @racketmodname[hackett] adds support for properly importing
bindings in the type namespace, but otherwise, the behavior is the same.}

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
    (foo1 t:Integer t:Bool)
    (foo2 t:String)
    foo3)
  (instance (t:Show Foo)
    [show (λ* [[(foo1 a b)] {"(foo1 " ++ (show a) ++ " "
                                      ++ (show b) ++ ")"}]
              [[(foo2 a)] {"(foo2 " ++ (show a) ++ ")"}]
              [[foo3] "foo3"])])
  (#:type foo1)
  (foo1 42 True)
  (#:type foo2)
  (foo2 "hello")
  foo3)

Additionally, the bound @racket[value-id]s and @racket[data-constructor-id]s serve as @tech{patterns}
that match against different values of the defined type. The pattern associated with each
@racket[data-constuctor-id] accepts patterns that match against the contained values, so
pattern-matching allows extracting values stored “inside” data constructors.

@(hackett-examples
  #:eval data-examples-eval
  (case (foo1 42 True)
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
  (instance (t:forall [a] (t:Show a) t:=> (t:Show (Tree a)))
    [show (λ* [[{a :&: b}] {"{" ++ (show a) ++ " :&: " ++ (show b) ++ "}"}]
              [[(leaf a)] {"(leaf " ++ (show a) ++ ")"}])])
  {(leaf 1) :&: (leaf 2) :&: (leaf 3)})}
@(close-eval data-examples-eval)

@subsection[#:tag "reference-numbers"]{Numbers}

@deftype[t:Integer]{

The type of arbitrary-precision integers. Just as with numbers in @hash-lang[] @racketmodname[racket],
integers will be represented as @tech[#:doc '(lib "scribblings/reference/reference.scrbl")]{fixnums},
machine integers, where possible. Values that exceed this range will automatically be promoted to
arbitrary-precision “bignums”.}

@deftogether[
 [@defthing[+ {t:Integer t:-> t:Integer t:-> t:Integer}]
  @defthing[- {t:Integer t:-> t:Integer t:-> t:Integer}]
  @defthing[* {t:Integer t:-> t:Integer t:-> t:Integer}]]]{

These functions provide simple, arbitrary-precision, integral arithmetic.}

@deftogether[
 [@defthing[> {t:Integer t:-> t:Integer t:-> t:Bool}]
  @defthing[< {t:Integer t:-> t:Integer t:-> t:Bool}]
  @defthing[>= {t:Integer t:-> t:Integer t:-> t:Bool}]
  @defthing[<= {t:Integer t:-> t:Integer t:-> t:Bool}]]]{

Comparison operators on integers.}

@deftype[t:Double]{

The type of double-precision IEEE 754 floating-point numbers, known as
@tech[#:doc '(lib "scribblings/reference/reference.scrbl")]{flonums} in @hash-lang[]
@racketmodname[racket].}

@deftogether[
 [@defthing[d+ {t:Double t:-> t:Double t:-> t:Double}]
  @defthing[d- {t:Double t:-> t:Double t:-> t:Double}]
  @defthing[d* {t:Double t:-> t:Double t:-> t:Double}]
  @defthing[d/ {t:Double t:-> t:Double t:-> t:Double}]]]{

These functions provide simple, floating-point arithmentic on @racket[t:Double]s.}

@subsection[#:tag "reference-strings"]{Strings}

@deftype[t:String]{

The type of strings, which can be constructed using string literals.}

@defthing[string-length {t:String t:-> t:Integer}]{

Returns the length of a string, in characters.

@(hackett-examples
  (eval:check (string-length "hello") 5)
  (eval:check (string-length "Λάμβδα") 6))}

@defthing[string-split {t:String t:-> t:String t:-> (t:List t:String)}]{

Splits a string on all instances of a separator string.

@(hackett-examples
  (string-split "," "1,2,3,4,5")
  (string-split "," ",2,,4,")
  (string-split "," ",,,,"))}

@subsection[#:tag "reference-functions"]{Functions}

@deftycon[(t:-> a b)]{

A type constructor of arity 2 that represents functions, where @racket[a] is the type of value the
function accepts as an argument, and @racket[b] is the type of the result. Functions of higher arities
are represented via @tech[#:key "curried"]{currying}.}

@defthing[id (t:forall [a] {a t:-> a})]{

The identity function. Returns its argument unchanged.}

@defthing[const (t:forall [a b] {a t:-> b t:-> a})]{

Accepts two arguments and returns the first, ignoring the second.

@(hackett-examples
  (eval:check (const "hello" "goodbye") "hello")
  (eval:check (const Unit (error! "never gets here")) Unit))}

@defthing[|.| (t:forall [a b c] {{b t:-> c} t:-> {a t:-> b} t:-> {a t:-> c}})]{

Function composition. Given two functions @racket[_f] and @racket[_g], then @racket[({_f |.| _g} _x)]
is equivalent to @racket[(_f (_g _x))].

@(hackett-examples
  (def add1AndDouble {(* 2) |.| (+ 1)})
  (eval:check (add1AndDouble 3) 8))}

@defthing[$ (t:forall [a b] {{a t:-> b} t:-> a t:-> b})]{

Function application as a binary operator. Not especially useful, since @racket[{_f $ _x}] is
equivalent to @racket[(_f _x)], but sometimes convenient when used higher-order.}

@defthing[& (t:forall [a b] {a t:-> {a t:-> b} t:-> b})]{

Reverse function application. This function is a flipped version of @racket[$] that accepts the
argument first and the function second.}

@defthing[flip (t:forall [a b c] {{a t:-> b t:-> c} t:-> b t:-> a t:-> c})]{

Produces a function with the same behavior as another function, but with its first two arguments
flipped.

@(hackett-examples
  (flip :: Nil 3))}

@subsection[#:tag "reference-quantification"]{Quantification and Constrained Types}

@deftogether[
 [@deftycon*[#:literals [t:=>]
             [(t:forall [var-id ...+] type)
              (t:forall [var-id ...+] constraint ...+ t:=> type)]]
  @deftycon*[#:literals [t:=>]
             [(t:∀ [var-id ...+] type)
              (t:∀ [var-id ...+] constraint ...+ t:=> type)]]]]{

Universal quantification over types. Within @racket[type], each @racket[var-id] is bound to a fresh,
universally quantified type.

The second form is a shorthand that provides a nicer syntax for types constructed with @racket[t:=>]
nested immediately within @racket[t:forall]: @racket[(t:forall [var-id ...] constraint ... t:=> type)]
is precisely equivalent to @racket[(t:forall [var-id ...] (t:=> [constraint ...] type))].}

@deftycon[(t:=> [constraint ...+] type)]{

Builds a type that includes typeclass constraints. The resulting type is equivalent to @racket[type],
with the requirement that each @racket[constraint] must hold.}

@subsection[#:tag "reference-unit"]{Unit}

@defdata[t:Unit Unit]{

The unit type. Values of type @racket[t:Unit] only have one possible value (ignoring @tech{bottom}),
@racket[Unit]. A value of type @racket[t:Unit] carries no information, so it is similar to @void-const
in @hash-lang[] @racketmodname[racket] or the @tt{void} return “type” in many C-like languages.}

@subsection[#:tag "reference-booleans"]{Booleans}

@defdata[t:Bool True False]{

The @deftech{boolean} type, representing two binary states.}

@defthing[not {t:Bool t:-> t:Bool}]{

Inverts the @tech{boolean} it is applied to; that is, produces @racket[False] when given @racket[True]
and produces @racket[True] when given @racket[False].}

@defthing[if (t:forall [a] {t:Bool t:-> a t:-> a t:-> a})]{

Performs case analysis on a @tech{boolean} value. If the supplied boolean is @racket[True], returns
its second argument; otherwise, returns its third argument.

Since Hackett is lazy, @racket[if] is an ordinary function, not a macro or special form, and it can be
used higher-order if desired.

@(hackett-examples
  (eval:check (if True "first" "second") "first")
  (eval:check (if False "first" "second") "second"))}

@defthing[\|\| {t:Bool t:-> t:Bool t:-> t:Bool}]{

Returns @racket[True] if its first argument is @racket[True]; otherwise, returns its second argument.
Notably, the second argument will not be evaluated at all if the first argument is @racket[True], but
the first argument will always be forced when the result is forced.

@(hackett-examples
  (eval:check {True \|\| True} True)
  (eval:check {False \|\| True} True)
  (eval:check {True \|\| False} True)
  (eval:check {False \|\| False} False)
  (eval:check {True \|\| (error! "never gets here")} True))}

@defthing[&& {t:Bool t:-> t:Bool t:-> t:Bool}]{

Returns @racket[False] if its first argument is @racket[False]; otherwise, returns its second
argument. Notably, the second argument will not be evaluated at all if the first argument is
@racket[False], but the first argument will always be forced when the result is forced.

@(hackett-examples
  (eval:check {True && True} True)
  (eval:check {False && True} False)
  (eval:check {True && False} False)
  (eval:check {False && False} False)
  (eval:check {False && (error! "never gets here")} False))}

@subsection[#:tag "reference-identity"]{The Identity Type}

@defmodule[hackett/data/identity]

@defdata[(t:Identity a) (Identity a)]{

A simple wrapper type with a variety of typeclass instances that defer to the value inside whenever
possible. Most useful for its @racket[t:Functor], @racket[t:Applicative], and @racket[t:Monad] instances,
which simply apply functions to the value inside the @racket[Identity] wrapper, making it serve as
a “no-op” wrapper of sorts.

@(hackett-interaction
  (Identity 5)
  (map (+ 1) (Identity 5))
  {(Identity (+ 1)) <*> (Identity 5)}
  {(Identity "hello, ") ++ (Identity "world")})}

@defproc[(run-identity [x (t:Identity a)]) a]{

Unwraps and returns the value inside an @racket[Identity] wrapper.

@(hackett-interaction
  (run-identity (Identity 5)))}

@subsection[#:tag "reference-tuples"]{Tuples}

@defdata[(t:Tuple a b) (Tuple a b)]{

The @deftech{tuple} type, which contains a pair of possibly heterogenous values.}

@defthing[fst (t:forall [a b] {(t:Tuple a b) t:-> a})]{

Extracts the first element of a @tech{tuple}.

@(hackett-examples
  (eval:check (fst (Tuple 42 "hello")) 42))}

@defthing[snd (t:forall [a b] {(t:Tuple a b) t:-> b})]{

Extracts the second element of a @tech{tuple}.

@(hackett-examples
  (eval:check (snd (Tuple 42 "hello")) "hello"))}

@subsection[#:tag "reference-optionals"]{Optionals}

@defdata[(t:Maybe a) (Just a) Nothing]{

A type that encodes the notion of an optional or nullable value. A value of type @racket[(t:Maybe a)]
implies that it @emph{might} contain a value of type @racket[a], but it also might contain nothing at
all. This type is usually used to represent operations that can fail (where @racket[Nothing]
represents failure) or values that are not required to be present.

@(hackett-examples
  (map (+ 1) (Just 5))
  (map (+ 1) Nothing))}

@defproc[(maybe [v b] [f {a t:-> b}] [x (t:Maybe a)]) b]{

The catamorphism for @racket[t:Maybe]. Produces @racket[v] when @racket[x] is @racket[Nothing] and
produces @racket[(f _y)] when @racket[x] is @racket[(Just _y)].

@(hackett-examples
  (eval:check (maybe 0 (+ 1) (Just 5)) 6)
  (eval:check (maybe 0 (+ 1) Nothing) 0))}

@defproc[(from-maybe [v a] [x (t:Maybe a)]) a]{

Extracts the value inside @racket[x], producing a default value @racket[v] when @racket[x] is
@racket[Nothing]. Equivalent to @racket[(maybe v id)].

@(hackett-examples
  (eval:check (from-maybe 0 (Just 5)) 5)
  (eval:check (from-maybe 0 Nothing) 0))}

@defdata[(t:Either a b) (Left a) (Right b)]{

A type that encodes the notion of a successful result or an error. The @racket[t:Functor],
@racket[t:Applicative], and @racket[t:Monad] instances for @racket[(t:Either a)] are “right-biased”, so
they will short-circuit on values wrapped in @racket[Left] and will perform mapping or sequencing on
values wrapped in @racket[Right].

This type is generally used in a similar way to @racket[t:Maybe], but it allows the sort of failure to
be explicitly tagged, usually returning a error message or failure reason on the @racket[Left] side.

@(hackett-examples
  (map (+ 1) (: (Right 5) (t:Either t:String t:Integer)))
  (map (+ 1) (: (Left "an error happened") (t:Either t:String t:Integer))))}

@defproc[(either [f {a t:-> c}] [g {b t:-> c}] [x (t:Either a b)]) c]{

The catamorphism for @racket[t:Either]. Produces @racket[(f _y)] when @racket[x] is @racket[(Left _y)]
and produces @racket[(g _z)] when @racket[x] is @racket[(Right _z)].

@(hackett-examples
  (eval:check (either (+ 1) (* 2) (Left 5)) 6)
  (eval:check (either (+ 1) (* 2) (Right 5)) 10))}

@defproc[(is-left [e (t:Either a b)]) t:Bool]{

This predicate is @racket[True] when @racket[e] is of the form @racket[(Left x)] for some @racket[x],
and is @racket[False] when @racket[e] is @racket[(Right x)].

@(hackett-examples
  (eval:check (is-left (Left "nifty")) True)
  (eval:check (is-left (Right "tubular")) False))}

@defproc[(is-right [e (t:Either a b)]) t:Bool]{

This predicate is @racket[True] when @racket[e] is of the form @racket[(Right x)] for some @racket[x],
and is @racket[False] when @racket[e] is @racket[(Left x)].

@(hackett-examples
  (eval:check (is-right (Left "nifty")) False)
  (eval:check (is-right (Right "tubular")) True))}

@defproc[(lefts [es (t:List (t:Either a b))]) (t:List a)]{

Extract all values of the form @racket[(Left x)] from es.

@(hackett-examples
  (lefts {(Left 1) :: (Right "haskell") :: (Right "racket") :: (Left -32) :: Nil}))}

@defproc[(rights [es (t:List (t:Either a b))]) (t:List b)]{

Extract all values of the form @racket[(Right x)] from es.

@(hackett-examples
  (rights {(Left 1) :: (Right "haskell") :: (Right "racket") :: (Left -32) :: Nil}))}

@defproc[(partition-eithers [es (t:List (t:Either a b))]) (t:Tuple (t:List a) (t:List b))]{

Extract every @racket[(Left x)] to the first element of the pair and each @racket[(Right x)] to the
second. @racket[(partition-eithers es)] is equivalent to @racket[(Tuple (lefts es) (rights es))]

@(hackett-examples
  (partition-eithers {(Left 1) :: (Right "haskell") :: (Right "racket") :: (Left -32) :: Nil}))}

@subsection[#:tag "reference-lists"]{Lists}

@defdata[(t:List a) (:: a (t:List a)) Nil]{

The @deftech{list} type, which describes lazy linked lists. Since a list is lazy, it may be infinite,
as long as the entire list is never demanded. The @racket[::] constructor is pronounced “cons”, and it
is generally intended to be used infix.}

@defproc[(head [xs (t:List a)]) (t:Maybe a)]{

Returns @racket[Just] the first element of @racket[xs], or @racket[Nothing] if @racket[xs] is @racket[Nil].

@(hackett-examples
  (head {1 :: 2 :: 3 :: Nil})
  (head (: Nil (t:List t:Integer))))}

@defproc[(last [xs (t:List a)]) (t:Maybe a)]{

Returns @racket[Just] the last element of @racket[xs], or @racket[Nothing] if @racket[xs] is @racket[Nil].
This function is @tech[#:key "partial function"]{partial}, since it diverges on an infinitely long
input, e.g. @racket[(letrec ([ones {1 :: ones}]) (last ones))].

@(hackett-examples
  (last {1 :: 2 :: 3 :: Nil})
  (last (: Nil (t:List t:Integer))))}

@defproc[(tail [xs (t:List a)]) (t:Maybe (t:List a))]{

Returns @racket[Just] @racket[xs] without its first element, or @racket[Nothing] if @racket[xs] is
@racket[Nil].

@(hackett-examples
  (tail {1 :: 2 :: 3 :: Nil})
  (tail (: Nil (t:List t:Integer))))}

@defproc[(init [xs (t:List a)]) (t:Maybe a)]{

Returns @racket[Just] @racket[xs] without its the last element, or @racket[Nothing] if @racket[xs] is
@racket[Nil]. This function is @tech[#:key "partial function"]{partial}, since it diverges on an
infinitely long input, e.g. @racket[(letrec ([ones {1 :: ones}]) (init ones))].

@(hackett-examples
  (init {1 :: 2 :: 3 :: Nil})
  (init (: Nil (t:List t:Integer))))}

@defproc[(head! [xs (List a)]) a]{

A @tech[#:key "partial function"]{partial} version of @racket[head] which returns the first element of
@racket[xs]. If @racket[xs] is empty, @racket[head!] raises an error.

@(hackett-examples
  (head! {1 :: 2 :: 3 :: Nil})
  (eval:error (head! (: Nil (t:List t:Integer)))))}

@defproc[(last! [xs (t:List a)]) a]{

A less-safe version of @racket[last] which returns the last element of @racket[xs]. This function
is @tech[#:key "partial function"]{partial}, since when @racket[xs] is empty, @racket[last!] raises
an error, and if @racket[xs] is infinitely long, @racket[last!] will never return.

@(hackett-examples
  (last! {1 :: 2 :: 3 :: Nil})
  (eval:error (last! (: Nil (t:List t:Integer)))))}

@defproc[(tail! [xs (t:List a)]) (t:List a)]{

A @tech[#:key "partial function"]{partial} version of @racket[tail] that returns @racket[xs] without
its first element. If @racket[xs] is empty, @racket[tail!] raises an error.

@(hackett-examples
  (tail! {1 :: 2 :: 3 :: Nil})
  (eval:error (tail! (: Nil (t:List t:Integer)))))}

@defproc[(init! [xs (t:List a)]) a]{

A less-safe version of @racket[init] which returns the last element of @racket[xs]. This function
is @tech[#:key "partial function"]{partial}, since when @racket[xs] is empty, @racket[init!] raises an
error, and if @racket[xs] is infinitely long, @racket[init!] will never return.

@(hackett-examples
  (init! {1 :: 2 :: 3 :: Nil})
  (eval:error (init! (: Nil (t:List t:Integer)))))}

@defproc[(uncons [xs (t:List a)]) (t:Maybe (t:Tuple a (t:List a)))]{

When @racket[xs] is @racket[Nil], @racket[uncons xs] is @racket[Nothing]. Otherwise, if @racket[xs]
is @racket[{y :: ys}] then @racket[uncons xs] is @racket[Just (Tuple y ys)].

@(hackett-examples
  (uncons {1 :: 2 :: 3 :: Nil})
  (uncons (: Nil (t:List t:Integer))))}

@defproc[(uncons! [xs (t:List a)]) (t:Tuple a (t:List a))]{

A @tech[#:key "partial function"]{partial} version of @racket[uncons] that returns
@racket[Tuple (head! xs) (tail! xs)]. If @racket[xs] is empty, it instead raises an error.

@(hackett-examples
  (uncons! {1 :: 2 :: 3 :: Nil})
  (eval:error (uncons! (: Nil (t:List t:Integer)))))}

@defproc[(nil? [xs (t:List a)]) (t:Bool)]{

This predicate is @racket[True] when @racket[xs] is of the form @racket[Nil], and is false otherwise.

@(hackett-examples
  (nil? {1 :: 2 :: 3 :: Nil})
  (nil? (: Nil (t:List t:Integer))))}

@defproc[(length [xs (t:List a)]) t:Integer]{

Returns the length of @racket[xs] when @racket[xs] is finite. Since the function diverges on an
infinitely long input, @racket[length] is @tech[#:key "partial function"]{partial}.

@(hackett-examples
  (length {1 :: 2 :: 3 :: Nil})
  (length (: Nil (t:List t:Integer))))}

@defproc[(take [n t:Integer] [xs (t:List a)]) (t:List a)]{

Produces a list with the first @racket[n] elements of @racket[xs]. If @racket[xs] contains fewer than
@racket[n] elements, @racket[xs] is returned unmodified.

@(hackett-examples
  (take 2 {1 :: 2 :: 3 :: Nil})
  (take 2 {1 :: Nil})
  (take 2 (: Nil (t:List t:Integer))))}

@defproc[(drop [n t:Integer] [xs (t:List a)]) (t:List a)]{

Produces a list like @racket[xs] without its first @racket[n] elements. If @racket[xs] contains fewer
then @racket[n] elements, the result is @racket[Nil].

@(hackett-examples
  (drop 2 {1 :: 2 :: 3 :: Nil})
  (drop 2 {1 :: Nil})
  (drop 2 (: Nil (t:List t:Integer))))}

@defproc[(filter [f {a t:-> t:Bool}] [xs (t:List a)]) (t:List a)]{

Produces a list that contains each element, @racket[_x], for which @racket[_x] is an element of
@racket[xs] and @racket[(f _x)] is @racket[True].

@(hackett-examples
  (filter (λ [x] {x > 5}) {3 :: 7 :: 2 :: 9 :: 12 :: 4 :: Nil}))}

@defproc[(foldr [f {a t:-> b t:-> b}] [acc b] [xs (t:List a)]) b]{

Reduces @racket[xs] to a single value using a right-associative binary operator, @racket[f], using
@racket[acc] as a “seed” element. Uses of @racket[foldr] can be thought of as a series of nested,
right-associative applications of @racket[f], so if @racket[xs] contains elements named @racket[_x0],
@racket[_x1], @racket[_x2] etc., up to @racket[_xn], then @racket[(foldr f acc xs)] is equivalent to
the following expression:

@(racketblock
  {_x0 f {_x1 f {_x2 f .... {_xn f acc} ....}}})

@(hackett-examples
  (foldr + 0 {1 :: 2 :: 3 :: 4 :: 5 :: Nil})
  (foldr * 1 {1 :: 2 :: 3 :: 4 :: 5 :: Nil})
  (foldr - 0 {1 :: 2 :: 3 :: 4 :: 5 :: Nil})
  (foldr :: Nil {1 :: 2 :: 3 :: 4 :: 5 :: Nil}))}

@defproc[(foldl [f {b t:-> a t:-> b}] [acc b] [xs (t:List a)]) b]{

Reduces @racket[xs] to a single value using a left-associative binary operator, @racket[f], using
@racket[acc] as a “seed” element. Uses of @racket[foldr] can be thought of as a series of nested,
left-associative applications of @racket[f], so if @racket[xs] contains elements named @racket[_x0],
@racket[_x1], @racket[_x2] etc., up to @racket[_xn], then @racket[(foldr f acc xs)] is equivalent to
the following expression:

@(racketblock
  {.... {{{acc f _x0} f _x1} f _x2} .... _xn})

@(hackett-examples
  (foldl + 0 {1 :: 2 :: 3 :: 4 :: 5 :: Nil})
  (foldl * 1 {1 :: 2 :: 3 :: 4 :: 5 :: Nil})
  (foldl - 0 {1 :: 2 :: 3 :: 4 :: 5 :: Nil}))}

@defproc[(sum [xs (t:List t:Integer)]) t:Integer]{

Adds the elements of @racket[xs] together and returns the sum. Equivalent to @racket[(foldl + 0)].

@(hackett-examples
  (eval:check (sum {1 :: 2 :: 3 :: Nil}) 6)
  (eval:check (sum Nil) 0))}

@defproc[(reverse (xs (t:List a))) (t:List a)]{

Returns @racket[xs] in reversed order.

@(hackett-examples
 (reverse {1 :: 2 :: 3 :: Nil})
 (reverse (: Nil (t:List t:Integer))))}

@defproc[(zip-with [f {a t:-> b t:-> c}] [as (t:List a)] [bs (t:List b)]) (t:List c)]{

This function will apply @racket[f] to each element in @racket[as] and @racket[bs] until it
has reached the end of either, then it returns a list like
@racket[{f _a0 _b0 :: f _a1 _b1 :: f _a2 _b2 :: ... :: Nil}] (where @racket[as] contains
elements named @racket[_a0], @racket[_a1], @racket[_a2] etc., and @racket[bs] contains elements
named @racket[_b0], @racket[_b1], @racket[_b2] etc.).

@(hackett-examples
 (zip-with + {1 :: 2 :: 3 :: Nil} {18 :: 42 :: 50 :: Nil})
 (zip-with + {1 :: 2 :: 3 :: Nil} {18 :: 42 :: 50 :: 100 :: Nil})
 (zip-with + {1 :: 2 :: 3 :: 4 :: Nil} {18 :: 42 :: 50 :: Nil})
 (zip-with * {1 :: 2 :: 3 :: Nil} {18 :: 42 :: 50 :: Nil})
 (zip-with + (: Nil (t:List t:Integer)) (: Nil (t:List t:Integer))))}

@defproc[(zip [as (t:List a)] [bs (t:List b)]) (t:List (t:Tuple a b))]{

Returns a list of componenetwise pairs from @racket[as] and @racket[bs]. The length of this list is
the length of the shortest input list. Equivalent to @racket[(zip-with Tuple as bs)].

@(hackett-examples
 (zip {1 :: 2 :: 3 :: Nil} {18 :: 42 :: 50 :: Nil})
 (zip {1 :: 2 :: 3 :: Nil} {18 :: 42 :: 50 :: 100 :: Nil})
 (zip {1 :: 2 :: 3 :: 4 :: Nil} {18 :: 42 :: 50 :: Nil})
 (zip (: Nil (t:List t:Integer)) (: Nil (t:List t:Integer))))}

@defproc[(repeat [x a]) (t:List a)]{

Returns an infinite list containing only @racket[x].

@(hackett-examples
 (take 5 (repeat 1)))}

@defproc[(cycle! [xs (t:List a)]) (t:List a)]{

Returns the infinite list @racket[{xs ++ xs ++ xs ++ ...}]. If @racket[xs] is infinite,
@racket[cycle! xs == xs]. This function is @tech[#:key "partial function"]{partial},
because it errors when given @racket[Nil].

@(hackett-examples
 (take 10 (cycle! {1 :: 2 :: 3 :: Nil}))
 (eval:error (cycle! (: Nil (t:List t:Integer)))))}

@defproc[(or [xs (t:List t:Bool)]) t:Bool]{

Logically ors the elements of @racket[xs] together and returns the result. Equivalent to @racket[(foldr || False)].
Because it uses a right fold, the only elements which will be evaluated are those before the first expression which
evaluates to @racket[True]. Additionally, @racket[or infinite-list] can never return @racket[False], and
@racket[or (repeat False)] will never terminate.

@(hackett-examples
  (or {True :: False :: Nil})
  (or {False :: True :: Nil})
  (or {True :: (error! "never happens") :: Nil})
  (or Nil))}

@defproc[(and [xs (t:List t:Bool)]) t:Bool]{

Logically ands the elements of @racket[xs] together and returns the result. Equivalent to @racket[(foldr && True)].
Because it uses a right fold, the only elements which will be evaluated are those before the first expression which
evaluates to @racket[False]. Additionally, @racket[and infinite-list] can never return @racket[True], and
@racket[and (repeat True)] will never terminate.

@(hackett-examples
  (and {True :: False :: Nil})
  (and {False :: True :: Nil})
  (and {False :: (error! "never happens") :: Nil})
  (and Nil))}

@defproc[(any? [p {a t:-> t:Bool}] [xs (t:List t:Bool)]) t:Bool]{

Returns @racket[True] if @racket[xs] contains an element @racket[x] such that @racket[(p x)] is
@racket[True]. Equivalent to @racket[(or (map p xs))].

@(hackett-examples
  (any? (<= 2) {1 :: 2 :: 3 :: Nil})
  (any? (<= 4) {1 :: 2 :: 3 :: Nil})
  (any? (<= 0) {1 :: (error! "never happens") :: Nil})
  (any? (<= 0) Nil))}

@defproc[(all? [p {a t:-> t:Bool}] [xs (t:List t:Bool)]) t:Bool]{

Returns @racket[True] if for every element @racket[x] of @racket[xs] @racket[(p x)] is
@racket[True]. Equivalent to @racket[(and (map p xs))].

@(hackett-examples
  (all? (<= 1) {1 :: 2 :: 3 :: Nil})
  (all? (<= 2) {1 :: 2 :: 3 :: Nil})
  (all? (<= 2) {1 :: (error! "never happens") :: Nil})
  (all? (<= 1) Nil))}

@defproc[(elem? [_ (t:Eq a)] [x a] [xs (t:List a)]) t:Bool]{

Returns @racket[True] if @racket[xs] contains @racket[x]. Equivalent to @racket[(any? (== x) xs)].
Only elements to the left of the first expression equal to @racket[x] in @racket[xs] will be checked
for equality.

@(hackett-examples
  (elem? 2 {1 :: 2 :: 3 :: Nil})
  (elem? 0 {1 :: 2 :: 3 :: Nil})
  (elem? 1 {1 :: (error! "never happens") :: Nil})
  (elem? 1 Nil))}

@defproc[(not-elem? [_ (t:Eq a)] [x a] [xs (t:List a)]) t:Bool]{

Returns @racket[False] if @racket[xs] contains @racket[x]. Equivalent to @racket[(not (elem? x xs))].
Only elements to the left of the first expression equal to @racket[x] in @racket[xs] will be checked
for equality.

@(hackett-examples
  (elem? 2 {1 :: 2 :: 3 :: Nil})
  (elem? 0 {1 :: 2 :: 3 :: Nil})
  (elem? 1 {1 :: (error! "never happens") :: Nil})
  (elem? 1 Nil))}

@defproc[(delete [_ (t:Eq a)] [x a] [xs (t:List a)]) (t:List a)]{

Returns @racket[xs] with the first occurrence of @racket[x] removed. Equivalent to
@racket[(delete-by == x xs)]. Only elements to the left of the first expression equal to @racket[x]
in @racket[xs] will be checked for equality.

@(hackett-examples
  (delete 2 {1 :: 2 :: 3 :: Nil})
  (delete 0 {1 :: 2 :: 3 :: Nil})
  (head (delete 1 {1 :: 2 :: (error! "never happens") :: Nil}))
  (delete 1 Nil))}

@defproc[(delete-by [rel {a t:-> a t:-> t:Bool}] [x a] [xs (t:List a)]) (t:List a)]{

Finds the first element @racket[y] such that @racket[{y rel x}] and returns @racket[xs] with
@racket[y] removed. Generalizes @racket[delete]. Only elements to the left of the first expression
such @racket[y] will be checked for equality.

@(hackett-examples
  (delete-by > 2 {1 :: 2 :: 3 :: Nil})
  (delete-by > 0 {1 :: 2 :: 3 :: Nil})
  (head (delete-by not= 1 {1 :: 2 :: (error! "never happens") :: Nil}))
  (delete-by (λ [y x] {(remainder! y x) == 0}) 2 Nil)
  (delete-by (error! "never happens") (error! "never happens") (: Nil (t:List t:Integer))))}

@defproc[(intersperse [x a] [xs (t:List a)]) (t:List a)]{

Given a separator and a list, intersperse intersperses the separator between each element of the list.

@(hackett-examples
 (intersperse 42 {1 :: 2 :: 3 :: Nil})
 (intersperse 42 Nil))}

@section[#:tag "reference-typeclasses"]{Typeclasses}

@subsection[#:tag "reference-defining-typeclasses"]{Defining typeclasses and typeclass instances}

@defform[#:literals [: t:=>]
         (class maybe-superclasses (class-id var-id ...)
           [method-id : method-type maybe-default-method-impl] ...)
         #:grammar
         ([maybe-superclasses (code:line superclass-constraint ... t:=>)
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

@defform[#:literals [t:forall t:=>]
         (instance instance-spec
           [method-id method-expr] ...)
         #:grammar
         ([instance-spec (class-id instance-type ...)
                         (t:forall [var-id ...] maybe-constraints
                                   (class-id instance-type ...))]
          [maybe-constraints (code:line instance-constraint ... t:=>)
                             (code:line)])]{

Defines a @deftech{typeclass instance}, which declares that the given @racket[instance-type]s belong
to the @tech{typeclass} bound to @racket[class-id].}

@subsection[#:tag "reference-show"]{Printing for debugging}

@defclass[(t:Show a)
          [show {a t:-> t:String}]]{

A class for converting values to @racket[t:String] representations for the purposes of debugging.
Generally, the @racket[t:Show] instance for a type should produce a valid Hackett expression that, when
evaluated, produces the value.

@defmethod[show {a t:-> t:String}]{

@(hackett-examples
  (show 42)
  (show "hello")
  (show (Just 11))
  (show {1 :: 2 :: 3 :: Nil}))}}

@subsection[#:tag "reference-equality"]{Equality}

@defclass[(t:Eq a)
          [== {a t:-> a t:-> t:Bool}]]{
The class of types with a notion of equality. The @racket[==] method should produce @racket[True] if
both of its arguments are equal, otherwise it should produce @racket[False].

@defmethod[== {a t:-> a t:-> t:Bool}]{

@(hackett-examples
  (eval:check {10 == 10} True)
  (eval:check {10 == 11} False)
  (eval:check {{1 :: 2 :: Nil} == {1 :: 2 :: Nil}} True)
  (eval:check {{1 :: 2 :: Nil} == {1 :: Nil}} False)
  (eval:check {{1 :: 2 :: Nil} == {1 :: 3 :: Nil}} False))}}

@subsection[#:tag "reference-semigroup-monoid"]{Semigroups and monoids}

@defclass[(t:Semigroup a)
          [++ {a t:-> a t:-> a}]]{

The class of @deftech{semigroups}, types with an associative binary operation, @racket[++]. Generally,
@racket[++] defines some notion of combining or appending, as is the case with the instances for
@racket[t:String] and @racket[(t:List _a)], but this is not necessarily true.

@defmethod[++ {a t:-> a t:-> a}]{

An associative operation. That is, @racket[++] must obey the following law:

@racketblock[
  @#,racket[{{_a ++ _b} ++ _c}] @#,elem[#:style 'roman]{=} @#,racket[{_a ++ {_b ++ _c}}]]

@(hackett-examples
  {"hello" ++ ", " ++ "world!"}
  {{1 :: 2 :: Nil} ++ {3 :: 4 :: Nil}})}}

@defclass[#:super [(t:Semigroup a)]
          (t:Monoid a)
          [mempty a]]{

A @deftech{monoid} extends the notion of a @tech{semigroup} with the notion of an identity element,
@racket[mempty].

@defmethod[mempty a]{

An identity element for @racket[++]. That is, @racket[mempty] must obey the following laws:

@racketblock[
  @#,racket[{_a ++ mempty}] @#,elem[#:style 'roman]{=} @#,racket[_a]
  @#,racket[{mempty ++ _a}] @#,elem[#:style 'roman]{=} @#,racket[_a]]

@(hackett-examples
  (: mempty t:String)
  (: mempty (t:List t:Integer)))}}

@subsection[#:tag "reference-functor"]{Functors}

@defclass[(t:Functor f)
          [map (t:forall [a b] {{a t:-> b} t:-> (f a) t:-> (f b)})]]{

A class of types that are @deftech{functors}, essentially types that provide a mapping or “lifting”
operation. The @racket[map] function can be viewed in different ways:

  @itemlist[
    @item{The @racket[map] function can be thought of as applying a function to each “element” of some
          “container”. This metaphor applies to many members of the @racket[t:Functor] typeclass, such
          as @racket[t:List] and @racket[t:Maybe], but does not apply well to all of them.}

    @item{More generally, @racket[map] can be viewed as a “lifting” operation, which “lifts” a
          function of type @racket[{_a t:-> _b}] to a function of type @racket[{(f _a) t:-> (f _b)}]
          for some type @racket[f]. This is a very general notion, and the meaning of such an
          operation is highly dependent on the particular choice of @racket[f].}]

All @racket[map] implementations must obey the following laws:

@racketblock[
  @#,racket[(map id)] @#,elem[#:style 'roman]{=} @#,racket[id]
  @#,racket[(map {_f |.| _g}) @#,elem[#:style 'roman]{=} @#,racket[{(map _f) |.| (map _g)}]]]

@defmethod[map (t:forall [a b] {{a t:-> b} t:-> (f a) t:-> (f b)})]{

@(hackett-examples
  (map (+ 1) {1 :: 2 :: Nil})
  (map (+ 1) (Just 10))
  (map (+ 1) Nothing))}}

@defthing[<$> (t:forall [f a b] (t:Functor f) t:=> {{a t:-> b} t:-> (f a) t:-> (f b)})]{

An alias for @racket[map], intended to be used in @tech{infix mode} instead of prefix, especially when
mixed with @racket[<*>] in the same expression.

@(hackett-examples
  {(+ 1) <$> {1 :: 2 :: Nil}}
  {(+ 1) <$> (Just 10)}
  {(+ 1) <$> Nothing})}

@defthing[<&> (t:forall [f a b] (t:Functor f) t:=> {(f a) t:-> {a t:-> b} t:-> (f b)})]{

A flipped version of @racket[<$>] for when it’s preferable to take the function argument second, like
@racket[&] but lifted to a @tech{functor}.}

@defthing[<$ (t:forall [f a b] (t:Functor f) t:=> {b t:-> (f a) t:-> (f b)})]{

Equivalent to @racket[{map |.| const}]. Replaces all values of type @racket[_a] with a new value of
type @racket[_b].

@(hackett-examples
  {10 <$ (Just 1)}
  {10 <$ {1 :: 2 :: 3 :: Nil}})}

@defthing[$> (t:forall [f a b] (t:Functor f) t:=> {(f a) t:-> b t:-> (f b)})]{

A flipped version of @racket[<$].}

@defthing[ignore (t:forall [f a] (t:Functor f) t:=> {(f a) t:-> (f t:Unit)})]{

Replaces the result of a @tech{functor} with @racket[Unit]. Equivalent to @racket[(<$ Unit)].}

@subsection[#:tag "reference-applicative"]{Applicative functors}

@defclass[#:super [(t:Functor f)]
          (t:Applicative f)
          [pure (t:forall [a] {a t:-> (f a)})]
          [<*> (t:forall [a b] {(f {a t:-> b}) t:-> (f a) t:-> (f b)})]]{

The class of @deftech{applicative functors}, which are @tech{functors} with some notion of
application, @racket[<*>]. Additionally, applicative functors must provided a lifting operation,
@racket[pure], which embeds any value into @racket[f].

Applicative functors must satisfy the following laws:

@racketblock[
  @#,racket[{(pure id) <*> _v}] @#,elem[#:style 'roman]{=} @#,racket[_v]
  @#,racket[{(pure |.|) <*> _u <*> _v <*> _w}] @#,elem[#:style 'roman]{=} @#,racket[{_u <*> (_v <*> _w)}]
  @#,racket[{(pure _f) <*> (pure _x)}] @#,elem[#:style 'roman]{=} @#,racket[(pure (_f _x))]
  @#,racket[{_u <*> (pure _y)}] @#,elem[#:style 'roman]{=} @#,racket[{(pure (& _y) <*> _u)}]]

As a consequence of these laws, the @racket[t:Functor] instance for @racket[f] will satisfy:

@racketblock[
  @#,racket[(map _f _x)] @#,elem[#:style 'roman]{=} @#,racket[{(pure _f) <*> _x}]]

@defmethod[pure (t:forall [a] {a t:-> (f a)})]{

Lifts a value.

@(hackett-examples
  (: (pure 11) (t:Maybe t:Integer))
  (: (pure 11) (t:List t:Integer)))}

@defmethod[<*> (t:forall [a b] {(f {a t:-> b}) t:-> (f a) t:-> (f b)})]{

Applies a function in a context. While @racket[map]/@racket[<$>] “lifts” a pure function to a function
that operates on a functor, @racket[<*>] applies a function that is already inside the context of a
@tech{functor}.

@(hackett-examples
  {(Just not) <*> (Just True)}
  {(Just not) <*> (Just False)}
  {(Just not) <*> Nothing}
  {(: Nothing (t:Maybe {t:Bool t:-> t:Bool})) <*> (Just True)})

Due to currying, this is especially useful in combination with @racket[<$>] to apply a multi-argument
function to multiple arguments within the context of some functor. For example, @racket[t:Maybe]
implements a sort of short-circuiting, where any @racket[Nothing] will cause the entire computation to
produce @racket[Nothing].

@(hackett-examples
  {+ <$> (Just 1) <*> (Just 2)}
  {+ <$> Nothing <*> (Just 2)}
  {+ <$> (Just 1) <*> Nothing})

This works because @racket[{_f <$> _x}] is guaranteed to be equivalent to @racket[{(pure _f) <*> _x}]
by the applicative laws, and since functions are curried, each use of @racket[<*>] applies a single
argument to the (potentially partially-applied) function.}}

@defthing[sequence (t:forall [f a] (t:Applicative f) t:=> {(t:List (f a)) t:-> (f (t:List a))})]{

Produces an action that runs a @tech{list} of @tech[#:key "applicative functor"]{applicative} actions
from left to right, then collects the results into a new list.

@(hackett-examples
  (sequence {(Just 1) :: (Just 2) :: (Just 3) :: Nil})
  (sequence {(Just 1) :: Nothing :: (Just 3) :: Nil}))}

@defthing[traverse
          (t:forall [f a b] (t:Applicative f) t:=> {{a t:-> (f b)} t:-> (t:List a) t:-> (f (t:List b))})]{

Applies a function to each element of a @tech{list} to produce an @tech[#:key "applicative functor"]{
applicative} action, then collects them left to right @italic{a la} @racket[sequence]
(@racket[(traverse _f _xs)] is equivalent to @racket[(sequence (map _f _xs))]).

@(hackett-examples
  (traverse head {{1 :: Nil} :: {2 :: 3 :: Nil} :: Nil})
  (traverse head {{1 :: Nil} :: Nil :: Nil}))}

@subsection[#:tag "reference-monad"]{Monads}

@defclass[#:super [(t:Applicative m)]
          (t:Monad m)
          [join (t:forall [a] {(m (m a)) t:-> (m a)})]
          [=<< (t:forall [a b] {{a t:-> (m b)} t:-> (m a) t:-> (m b)})]]{

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

@defmethod[join (t:forall [a] {(m (m a)) t:-> (m a)})]{

@(hackett-examples
  (join (Just (Just 3)))
  (join (Just (: Nothing (t:Maybe t:Integer))))
  (join (: Nothing (t:Maybe (t:Maybe t:Integer))))
  (join {{1 :: Nil} :: {2 :: 3 :: Nil} :: Nil}))}

@defmethod[=<< (t:forall [a b] {{a t:-> (m b)} t:-> (m a) t:-> (m b)})]{

Applies a function that produces a monadic value to a monadic value. The expression
@racket[{_f =<< _x}] is equivalent to @racket[(join {_f <$> _x})] (and an explicit implementation of
both methods must maintain that law). It is worth comparing and contrasting the types of
@racket[map]/@racket[<$>], @racket[<*>], and @racket[=<<], all of which are similar but slightly
different.

@(hackett-examples
  {head =<< (tail {1 :: 2 :: Nil})}
  {head =<< (tail {1 :: Nil})}
  {head =<< (tail (: Nil (t:List t:Integer)))})}}

@defthing[>>= (t:forall [m a b] (t:Monad m) t:=> {(m a) t:-> {a t:-> (m b)} t:-> (m b)})]{

A flipped version of @racket[=<<].}

@defform[#:literals [<-]
         (do do-clause ... monadic-expr)
         #:grammar
         ([do-clause [binding-id <- monadic-expr]
                     monadic-expr])]{

A convenient, imperative-style shorthand for a sequence of monadic expressions chained together with
@racket[>>=]. Each @racket[do-clause] corresponds to a single use of @racket[>>=], and each
@racket[monadic-expr] must have a type with the shape @racket[(_m _a)], where @racket[_m] is a
@racket[t:Monad].

Any use of @racket[do] with a single subform expands to the subform: @racket[(do _expr)] is equivalent
to @racket[_expr]. Each @racket[do-clause] introduces a use of @racket[>>=], with the result
potentially bound to a @racket[binding-id]. That is, @racket[(do [_x <- _m] _more ...+)] expands to
@racket[{_ma >>= (λ [_x] (do _more ...))}], and @racket[(do _m _more ...+)] expands to
@racket[{_ma >>= (λ [_] (do _more ...))}].

This is often much more readable than writing the uses of @racket[>>=] out by hand, especially when
the result of each action must be give a name.

@(hackett-examples
  (do [xs <- (tail {1 :: 2 :: 3 :: 4 :: Nil})]
      [ys <- (tail xs)]
      [zs <- (tail ys)]
      (head zs))
  (do [xs <- (tail {1 :: 2 :: 3 :: Nil})]
      [ys <- (tail xs)]
      [zs <- (tail ys)]
      (head zs)))}

@defthing[ap (t:forall [m a b] (t:Monad m) t:=> {(m {a t:-> b}) t:-> (m a) t:-> (m b)})]{

An implementation of @racket[<*>] in terms of @racket[map], @racket[pure], and @racket[join]. This can
be used as an implementation of @racket[<*>] as long as @racket[join] does not use @racket[<*>] (if it
does, the two will likely infinitely mutually recur).}

@section[#:tag "reference-io"]{I/O}

@deftycon[#:kind "type constructor" (t:IO a)]{

The type of @deftech{I/O actions}, which are @tech{monads}. Hackett’s encoding of I/O is semantically
pure—evaluating an I/O action does not cause any side-effects to be performed. The only way to
“execute” an I/O action is to provide it to the @racket[main] form, which instructs the Hackett
runtime to perform the actual I/O actions described by the @racket[t:IO] value.

It may be helpful to think of a value of type @racket[(t:IO a)] as a set of @emph{instructions} to
obtain a value of type @racket[a]. This makes it clear that it is @bold{impossible} to get the value
“inside” an @racket[t:IO] action, since no such value exists; there is no @racket[t:String] “inside” a
value of type @racket[(t:IO t:String)].

Since @racket[main] is the only way to ask the runtime to execute the instructions contained within
an @racket[t:IO] action, and @racket[main] is only legal at the top level of a module, it is
impossible for I/O to be performed locally. This is how Hackett preserves referential transparency
@emph{even within} functions that produce values of type @racket[t:IO].}

@defform[(main action)
         #:contracts
         ([action (t:IO _a)])]{

Appends an @tech{I/O action} to the current module’s @deftech{main actions}. Main actions are executed
by the runtime whenever a module is run directly, e.g. from DrRacket or via the @tt{racket}
executable, rather than imported via @racket[require]. This form is only legal at the top level of a
module.

Uses of this form correspond to definitions of @racketid[main] submodules in @hash-lang[]
@racketmodname[racket]. For more information, see
@secref["main-and-test" #:doc '(lib "scribblings/guide/guide.scrbl")].}

@defproc[(print [str t:String]) (t:IO t:Unit)]{

Produces an @tech{I/O action} that prints @racket[str] to standard output.}

@defproc[(println [str t:String]) (t:IO t:Unit)]{

Like @racket[print], but appends a newline to the end of the printed message.}

@section[#:tag "reference-monad-transformers"]{Monad Transformers}

@defmodule[hackett/monad/trans]

@defclass[(t:MonadTrans t)
          [lift (t:forall [m a] {(m a) t:-> (t m a)})]]{

The class of @deftech{monad transformers}. A monad transformer builds a new monad from an existing
one, extending it with additional functionality. In this sense, monad transformers can be thought of
as “monad mixins”.

Instances should satisfy the following laws:

@racketblock[
  @#,racket[{lift |.| pure}] @#,elem[#:style 'roman]{=} @#,racket[pure]
  @#,racket[(lift {_m >>= _f})] @#,elem[#:style 'roman]{=} @#,racket[{(lift _m) >>= {lift |.| _f}}]]

@defmethod[lift (t:forall [m a] {(m a) t:-> (t m a)})]{

Lifts a computation from the argument monad to the constructed monad.}}

@subsection[#:tag "reference-reader-monad"]{Reader}

@defmodule[hackett/monad/reader]

@defdata[(t:ReaderT r m a) (ReaderT {r t:-> (m a)})]{

The @deftech{reader monad transformer}, a @tech{monad transformer} that extends a monad with a
read-only dynamic environment. The environment can be accessed with @racket[ask] and locally modified
with @racket[local].

@(hackett-interaction
  (run-reader-t (do [x <- ask]
                    [y <- (lift {{x + 1} :: {x - 1} :: Nil})]
                    (lift {{y * 2} :: {y * 3} :: Nil}))
                10))}

@defproc[(run-reader-t [x (t:ReaderT r m a)] [ctx r]) (m a)]{

Runs the @tech{reader monad transformer} computation @racket[x] with the context @racket[ctx] and
produces a computation in the argument monad.}

@defproc[(run-reader [x (t:ReaderT r t:Identity a)] [ctx r]) a]{

Runs the @tech{reader monad transformer} computation @racket[x] with the context @racket[ctx] and
extracts the result.}

@defthing[ask (t:forall [r m] (t:ReaderT r m r))]{

A computation that fetches the value of the current dynamic environment.

@(hackett-interaction
  (eval:check (run-reader ask 5) 5)
  (eval:check (run-reader ask "hello") "hello"))}

@defproc[(asks [f {r t:-> a}]) (t:ReaderT r m a)]{

Produces a computation that fetches a value from the current dynamic environment, applies @racket[f]
to it, and returns the result.

@(hackett-interaction
  (eval:check (run-reader (asks (+ 1)) 5) 6)
  (eval:check (run-reader (asks head) {5 :: Nil}) (Just 5)))}

@defproc[(local [f {r t:-> r}] [x (t:ReaderT r m a)]) (t:ReaderT r m a)]{

Produces a computation like @racket[x], except that the environment is modified in its dynamic extent
by applying @racket[f] to it.}

@subsection[#:tag "reference-error-monad"]{Error}

@defmodule[hackett/monad/error]

@defdata[(t:ErrorT e m a) (ErrorT (m (t:Either e a)))]{

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

@defproc[(run-error-t [x (t:ErrorT e m a)]) (m (t:Either e a))]{

Runs the @tech{error monad transformer} computation @racket[x] and produces the possibly-aborted
result in the argument monad.}

@defproc[(run-error [x (t:ErrorT e t:Identity a)]) (t:Either e a)]{

Runs the @tech{error monad transformer} computation @racket[x] and extracts the possibly-aborted
result.}

@defproc[(throw [ex e]) (t:ErrorT e m a)]{

Produces a computation that raises @racket[ex] as an error, aborting the current computation (unless
caught with @racket[catch]).

@(hackett-interaction
  (eval:check (: (run-error (pure 42)) (t:Either t:String t:Integer))
              (: (Right 42) (t:Either t:String t:Integer)))
  (eval:check (run-error (do (throw "Ack!") (pure 42)))
              (: (Left "Ack!") (t:Either t:String t:Integer))))}

@defproc[(catch [x (t:ErrorT e m a)] [handler {e t:-> (t:ErrorT e* m a)}]) (t:ErrorT e* m a)]{

Produces a computation like @racket[x], except any errors raised are handled via @racket[handler]
instead of immediately aborting.

@(hackett-interaction
  (eval:check (: (run-error (throw "Ack!")) (t:Either t:String t:String))
              (: (Left "Ack!") (t:Either t:String t:String)))
  (eval:check (: (run-error (catch (throw "Ack!")
                              (λ [str] (pure {"Caught error: " ++ str}))))
                 (t:Either t:Unit t:String))
              (: (Right "Caught error: Ack!") (t:Either t:Unit t:String))))}

@section[#:tag "reference-controlling-evaluation"]{Controlling Evaluation}

@defthing[seq (t:forall [a b] {a t:-> b t:-> b})]{

Accepts two arguments and returns its second argument. When the result is forced, the first argument
will also be evaluated to weak head normal form. This can be used to reduce laziness.}

@defthing[error! (t:forall [a] {t:String t:-> a})]{

@see-guide-note["guide-bottoms"]{partial functions}

A simple @tech{partial function} that crashes the program with a message when evaluated.}

@defthing[undefined! (t:forall [a] a)]{

A @tech[#:key "partial function"]{partial} value that crashes the program when evaluated.}
