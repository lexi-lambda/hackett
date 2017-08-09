#lang scribble/manual

@(require scribblings/hackett/private/util)

@title[#:tag "guide" #:style 'toc]{The Hackett Guide}

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

@section[#:tag "guide-introduction"]{An introduction to Hackett}

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

@subsection[#:tag "guide-introduction-definitions"]{Simple Definitions}

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
