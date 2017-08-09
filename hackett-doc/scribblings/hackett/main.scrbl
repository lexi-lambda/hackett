#lang scribble/manual

@(require (for-label hackett)

          (for-syntax racket/base)

          racket/sandbox
          scribble/example
          scribble/manual/hackett
          syntax/parse/define)

@(define (make-hackett-eval [body '()])
   (parameterize ([sandbox-output 'string]
                  [sandbox-error-output 'string])
     (make-module-evaluator
      #:language 'hackett
      `(module m hackett
         ,@body))))

@(define-simple-macro (hackett-examples
                       {~or {~optional {~seq #:eval eval:expr}}
                            {~optional {~and #:once once}}
                            {~optional {~seq #:label label:expr}}}
                       ...
                       body ...)
   #:with eval* (or (attribute eval) #'(make-hackett-eval))
   #:with [once* ...] (cond [(attribute once) #'[once]]
                            [(attribute eval) #'[]]
                            [else             #'[#:once]])
   #:with [label* ...] (if (attribute label) #'[#:label label] #'[])
   (examples
    #:eval eval*
    once* ...
    label* ...
    body ...))

@(define-simple-macro (hackett-interaction body ...)
   (hackett-examples #:label #f body ...))

@title{The Hackett Programming Language}
@author{@author+email["Alexis King" "lexi.lambda@gmail.com"]}
@defmodule[hackett #:lang]

@table-of-contents[]

@section[#:tag "guide" #:style 'toc]{The Hackett Guide}

Hackett is a programming language in the Racket language ecosystem. Its name is a portmanteau that
hints at its philosophy and heritage:

@itemlist[
  @item{Like @hyperlink["https://www.haskell.org"]{Haskell}, Hackett is a purely functional,
        statically typed, lazily evaluated programming language. It provides powerful, bidirectional
        type inference, algebraic datatypes, pattern matching, typeclasses, and higher-rank
        polymorphism.}

  @item{Like @seclink["top" #:doc '(lib "scribblings/reference/reference.scrbl")]{Racket}, Hackett is
        a Lisp with an expressive hygienic macro system for compile-time metaprogramming and language
        extension. It is built as a tower of macros, and very few things are truly “baked into” the
        language and cannot be changed.}]

Hackett not only combines features from both Haskell and Racket, it interleaves and synthesizes them
to provide an even more powerful type system and even more powerful macros. Since the Hackett
typechecker is actually a part of macroexpansion, macros both have access to type information and can
influence the typechecking process.

This guide serves as a relatively gentle introduction to Hackett, and it assumes no prior experience
with either Haskell or Racket. Familiarity with either language will, of course, help.

@local-table-of-contents[]

@subsection[#:tag "guide-introduction"]{An introduction to Hackett}

The easiest way to get started with Hackett is by experimenting in the REPL. Using DrRacket, you can
quickly get a REPL by writing @hash-lang[] @racketmodname[hackett] at the top of the definitions
window and pressing the @onscreen{Run} button. Alternatively, if you can start a REPL from the
command-line by running the following command:

@commandline{racket -iI hackett}

Once you have a REPL started, you can try evaluating some simple expressions:

@(hackett-interaction
  3
  true)

Note that the result is printed out, such as @racketresultfont{3}, but so is the type, such as
@racket[Integer]. In Hackett, all valid expressions have a type, and the type can usually be inferred
by the typechecker.

The above expressions were very simple, just simple constants, so they are immediately returned
without any additional evaluation. Calling some functions is slightly more interesting:

@(hackett-interaction
  (eval:check (+ 1 2) 3)
  (eval:check (not true) false))

In Hackett, like any other Lisp, function calls are syntactically represented by surrounding
subexpressions with parentheses. In any expression @racket[(_f _x _y _z)], @racket[_f] is a function
expression to apply, and @racket[_x], @racket[_y], and @racket[_z] are arguments that will be passed
to the function.

So, what is a function? Well, a function is any value with a @deftech{function type}. For example,
it’s possible to see the type of @racket[not] by evaluating it in the REPL:

@(hackett-interaction
  not)

The type of @racket[not] is a @tech{function type}, which is represented by @racket[->]. The type can
be read as “a function that takes a @racket[Bool] and produces (or returns) a @racket[Bool]”. If you
attempt to apply something that is not a function, like @racket[3], the typechecker will reject the
expression as ill-typed:

@(hackett-interaction
  (eval:error (3 true)))

The type of @racket[+] is slightly more complicated:

@(hackett-interaction
  +)

This type has two @racket[->] constructors in it, and it actually represents a function that
@emph{returns} another function. This is because all functions in Hackett are @deftech{curried}—that
is, all functions actually only take a single argument, and multi-argument functions are simulated by
writing functions that return other functions.

To make this easier to understand, it may be helpful to observe the following expressions and their
types:

@(hackett-interaction
  +
  (+ 1)
  ((+ 1) 2))

This technique of representing multi-argument functions with single-argument functions scales to any
finite number of arguments, and it aids reuse and function composition by simplifying function types
and making it easy to partially apply functions.

Remember that, although @racket[+] is curried, it was possible to successfully evaluate
@racket[(+ 1 2)], which produces the same result as @racket[((+ 1) 2)]. This is because, in Hackett,
@racket[(_f _x _y)] is automatically translated to @racket[((_f _x) _y)]. The same pattern of nesting
also applies to any number of arguments greater than two. This makes applying multi-argument functions
considerably more palatable, as otherwise the number of parentheses required by nested applications
would be difficult to visually parse.

@subsubsection[#:tag "guide-introduction-definitions"]{Simple Definitions}

Simply evaluating expressions is not terribly exciting. For any practical program it is necessary to
be able to write your own definitions. A binding can be defined with the @racket[def] form:

@(hackett-interaction
  (def x 5)
  (eval:check (* x x) 25))

All bindings in Hackett are immutable: once something has been defined, its value cannot be changed.
This may sound like a severe limitation, but it is not as austere as you might think. In practice, it
is not only possible but often pleasant to write entire programs without mutable variables.

Definitions with @racket[def] are simple enough, but it is much more interesting to define functions.
This can be accomplished using the similar @racket[defn] form:

@margin-note{
  Those familiar with languages with first-class functions may find this distinction between
  @racket[def] and @racket[defn] unsatisfying. Indeed, @racket[defn] is just a shorthand for a useful,
  common combination of @racket[def], @racket[lambda], and @racket[case*]. Using @racket[defn] to
  define functions is, however, much preferred.}

@(define square-no-sig-eval (make-hackett-eval))

@(hackett-interaction
  #:eval square-no-sig-eval
  (defn square
    [[x] (* x x)])
  (eval:check (square 5) 25))

This defines a one-argument function called @racket[square], which (unsurprisingly) squares its
argument. Notably, we did not provide a type signature for @racket[square], but its type was still
successfully inferred. We can see the inferred type by evaluating it in the REPL:

@(hackett-interaction
  #:eval square-no-sig-eval
  square)

@(close-eval square-no-sig-eval)

Even though type signatures are not usually required, it’s generally a good idea to provide type
annotations for all top-level definitions. Even when the types can be inferred, adding explicit
signatures to top-level bindings helps to produce much more understandable type errors, and they can
serve as extremely useful documentation to people reading the code.

It’s possible to add a type signature to any definition by placing a type annotation after its name:

@(hackett-interaction
  (defn square : (-> Integer Integer)
    [[x] (* x x)])
  (eval:check (square 5) 25))

This definition is equivalent to the previous definition of @racket[square], but its type is validated
by the typechecker. If a type annotation is provided, but the expression does not actually have the
expected type, the typechecker will raise an error at compile time:

@(hackett-interaction
  (eval:error (def x : Integer "not an integer")))

@section[#:tag "reference" #:style 'toc]{The Hackett Reference}

This section provides reference-style documentation for all of the bindings provided by @hash-lang[]
@racketmodname[hackett] and other built-in libraries. It is arranged by module, not by topic. For a
gentler, more tutorial-style introduction to Hackett and its features, see @secref["guide"].

@local-table-of-contents[]

@subsection[#:tag "reference-syntactic-forms"]{Core Syntactic Forms}

@subsubsection[#:tag "reference-type-annotation"]{Type Annotation}

@defform[(: expr type)]{

Annotates @racket[expr] with @racket[type]. If @racket[expr] does not have the given type, a type
error is produced.

@(hackett-examples
  (: 42 Integer)
  (: "hello" String)
  (eval:error (: "hello" Integer)))

Additionally, some forms (such as @racket[def] and @racket[defn]) recognize literal uses of @racket[:]
to provide additional locations for type annotations.}

@subsubsection[#:tag "reference-definitions"]{Definitions}

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

@subsubsection[#:tag "reference-anonymous-functions"]{Anonymous Functions}

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

@subsubsection[#:tag "reference-pattern-matching"]{Pattern Matching}

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

@subsection[#:tag "reference-datatypes"]{Datatypes}

@subsubsection[#:tag "reference-algebraic-datatypes"]{Defining algebraic datatypes}

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

@subsubsection[#:tag "reference-numbers"]{Numbers}

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

@subsubsection[#:tag "reference-strings"]{Strings}

@defidform[#:kind "type" String]{

The type of strings, which can be constructed using string literals.}

@subsubsection[#:tag "reference-functions"]{Functions}

@defform[#:kind "type constructor" (-> a b)]{

A type constructor of arity 2 that represents functions, where @racket[a] is the type of value the
function accepts as an argument, and @racket[b] is the type of the result. Functions of higher arities
are represented via @tech[#:key "curried"]{currying}.}

@subsubsection[#:tag "reference-unit"]{Unit}

@defdata[Unit unit]{

The unit type. Values of type @racket[Unit] only have one possible value (ignoring @tech{bottom}),
@racket[unit]. A value of type @racket[unit] carries no information, so it is similar to @void-const
in @hash-lang[] @racketmodname[racket] or the @tt{void} return “type” in many C-like languages.}

@subsubsection[#:tag "reference-booleans"]{Booleans}

@defdata[Bool true false]{

The boolean type, representing two binary states.}

@defthing[not {Boolean -> Boolean}]{

Inverts the value it is applied to; this is, produces @racket[false] when given @racket[true] and
produces @racket[true] when given @racket[false].}

@subsubsection[#:tag "reference-optionals"]{Optionals}

@defdata[(Maybe a) (just a) nothing]{

A type that encodes the notion of an optional or nullable value. A value of type @racket[(Maybe a)]
implies that it @emph{might} contain a value of type @racket[a], but it also might contain nothing at
all. This type is usually used to represent operations that can fail (where @racket[nothing]
represents failure) or values that are not required to be present.}

@index-section[]
