#lang scribble/manual

@(require scribble/bnf
          scribblings/hackett/private/util)

@title[#:tag "guide" #:style 'toc]{The Hackett Guide}

Hackett is a high-level, general-purpose programming language designed for writing programs in many
domains, and it is designed to scale nicely from small programs to large, complex systems. Its name is
a portmanteau that hints at its philosophy and heritage:

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

@section[#:tag "guide-quick-start"]{Quick Start}

The easiest way to get started with Hackett is by experimenting in the REPL. Using DrRacket, you can
quickly get a REPL by writing @hash-lang[] @racketmodname[hackett] at the top of the definitions
window and pressing the @onscreen{Run} button. Alternatively, you can start a REPL from the
command-line by running the following command:

@commandline{racket -iI hackett}

Once you have a REPL started, you can try evaluating some simple expressions:

@(hackett-interaction
  3
  True)

Note that the result is printed out, such as @racketresultfont{3}, but so is the type, such as
@racket[t:Integer]. In Hackett, all valid expressions have a type, and the type can usually be
inferred by the typechecker.

The above expressions were very simple, just simple constants, so they are immediately returned
without any additional evaluation. Calling some functions is slightly more interesting:

@(hackett-interaction
  (eval:check (+ 1 2) 3)
  (eval:check (not True) False))

In Hackett, like any other Lisp, function calls are syntactically represented by surrounding
subexpressions with parentheses. In any expression @racket[(_f _x _y _z)], @racket[_f] is a function
expression to apply, and @racket[_x], @racket[_y], and @racket[_z] are arguments that will be passed
to the function.

So, what is a function? Well, a function is any value with a @deftech{function type}. We could try to
look at the type of @racket[not] by evaluating it in the REPL, but that will produce an error, since
functions aren’t printable:

@(hackett-interaction
  #:no-preserve-source-locations
  (eval:error not))

However, we can ask Hackett to only print the type of an expression by wrapping it with
@racket[(#:type _expr)], which will allow us to inspect the type of @racket[not]:

@(hackett-interaction
  (#:type not))

The type of @racket[not] is a @tech{function type}, which is represented by @racket[t:->]. The type
can be read as “a function that takes a @racket[t:Bool] and produces (or returns) a @racket[t:Bool]”.
If you attempt to apply something that is not a function, like @racket[3], the typechecker will reject
the expression as ill-typed:

@(hackett-interaction
  #:no-preserve-source-locations
  (eval:error (3 True)))

The type of @racket[+] is slightly more complicated:

@(hackett-interaction
  (#:type +))

This type has two @racket[t:->] constructors in it, and it actually represents a function that
@emph{returns} another function. This is because all functions in Hackett are @deftech{curried}—that
is, all functions actually only take a single argument, and multi-argument functions are simulated by
writing functions that return other functions.

To make this easier to understand, it may be helpful to observe the following expressions and their
types:

@(hackett-interaction
  (#:type +)
  (#:type (+ 1))
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

@subsection[#:tag "guide-quick-start-definitions"]{Simple Definitions}

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
  (#:type square))

@(close-eval square-no-sig-eval)

Even though type signatures are not usually required, it’s generally a good idea to provide type
annotations for all top-level definitions. Even when the types can be inferred, adding explicit
signatures to top-level bindings helps to produce much more understandable type errors, and they can
serve as extremely useful documentation to people reading the code.

It’s possible to add a type signature to any definition by placing a type annotation after its name:

@(hackett-interaction
  (defn square : (t:-> t:Integer t:Integer)
    [[x] (* x x)])
  (eval:check (square 5) 25))

This definition is equivalent to the previous definition of @racket[square], but its type is validated
by the typechecker. If a type annotation is provided, but the expression does not actually have the
expected type, the typechecker will raise an error at compile time:

@(hackett-interaction
  #:no-preserve-source-locations
  (eval:error (def x : t:Integer "not an integer")))

@section[#:tag "guide-hackett-essentials"]{Hackett Essentials}

Before leaping into Hackett’s language features, this section will establish some essential concepts
and terminology. Readers already familiar with both Scheme and Haskell can safely skip this section,
but it can be a useful overview.

Hackett, like most programming languages, is a language for manipulation of @deftech{values}. A value
is anything that exists at runtime, like a number, a string, a list, or a function. Every valid
Hackett value also has a @deftech{type}, which can be thought of as a “description” of the value. When
an expression is evaluated in the Hackett REPL, the value’s type will be printed just before the value
itself:

@(hackett-interaction
  42
  "Hello, world!")

Generally, a single type describes many values, sometimes infinitely many! Hackett can represent any
integer that will fit in memory, and all of them have the @racket[t:Integer] type. Similarly, there
are infinitely many possible arrangements of characters, and all of them have the @racket[t:String]
type.

In Hackett, types are @emph{exclusively} a compile-time concept; they never persist at runtime. After
a program has passed the typechecker, type information is thrown away; this process is known as
@deftech{type erasure}. It is not possible to dynamically query the type of a value at runtime, since
that information simply does not exist. Type erasure is possible because any program that would
incorrectly use a value as the wrong type will be detected and prevented by the typechecker; programs
that pass the typechecking process are considered @deftech{well-typed}.

Hackett programs are built out of series of nested @deftech{function applications}, which have the
following syntax:

@specform[(_function-expr arg-expr)]{

@(hackett-examples
  (not True)
  (not (not True))
  ((+ 1) 2))}

The above syntax @italic{applies} @racket[_function-expr] to @racket[_arg-expr], evaluating to the
function’s body. As mentioned in @secref["guide-quick-start"], Hackett functions are @tech{curried},
which means they only ever take a single argument, but multi-argument functions are simulated by
functions that return other functions. To make curried functions more pleasant to work with, function
application syntax actually accepts more than one argument at a time:

@specform[(_function-expr arg-expr ...+)]{

@(hackett-examples
  (+ 1 2))}

This syntax will be translated into a sequence of nested function applications, each of which only
involves application of a single @racket[_arg-expr] at a time.

In certain locations in Hackett programs, such as when providing a type annotation using @racket[:],
the programmer is expected to specify a type rather than a value. The syntax of types is similar to
the syntax of values, but be careful to never confuse the two: remember that types are evaluated at
compile-time, and they will never mix with runtime values, they simply describe them.

The simplest types are just names. For example, @racket[t:Integer], @racket[t:Bool], and
@racket[t:String] are all types. These can be successfully used anywhere a type is expected:

@(hackett-interaction
  (: 42 t:Integer)
  (: False t:Bool))

Some types, however, are more complex. For example, consider the type of a @tech{list}. It would be
silly to have many different types for all the different sorts of list one might need—that would
require completely separate types for things like @racket[Integer-List], @racket[Bool-List], and
@racket[String-List]. Instead, there is only a single @racket[t:List] type, but @racket[t:List] is not
actually a type on its own. Rather, @racket[t:List] is combined with another type to produce a new
type, such as @racket[(t:List t:Integer)] or @racket[(t:List t:String)].

This means that @racket[t:List] isn’t really a type, since types describe values, and @racket[t:List]
is not a valid type on its own. Instead, @racket[t:List] is known as a @deftech{type constructor},
which can be applied to other types to produce a type.

@subsection[#:tag "guide-infix-syntax"]{Infix Syntax}

Hackett supports a limited form of infix syntax, which allows binary functions (that is, functions
that accept two arguments) to be applied by placing the function between its two operands, rather than
before them as in the usual prefix notation generally used by Hackett. This means that a function
application of the following form:

@(racketblock
  @#,BNF-seq[@litchar{(} @nonterm{function expr} @nonterm{arg expr} @nonterm{arg expr} @litchar{)}])

…can be equivalently written in an alternate form:

@(racketblock
  @#,BNF-seq[
    @litchar{@"{"} @nonterm{arg expr} @nonterm{function expr} @nonterm{arg expr} @litchar{@"}"}])

Note the curly braces (@litchar{@"{}"}), which are significant in Hackett. When used as expressions,
parentheses and curly braces are @emph{not} interchangeable. Use of curly braces in an expression
enters @deftech{infix mode}, which alters function application syntax to support infix syntax.

Infix syntax is most useful for presenting mathematical notation, which is traditionally written using
infix symbolic operators. Hackett’s infix syntax can emulate this:

@(hackett-interaction
  (eval:check {1 + 2} 3)
  (eval:check {2 * 3} 6))

Any function of arity two can be applied using infix syntax, even those defined as entirely normal
functions; there is no syntactic difference between an “operator” and any other function. For example,
it would be equally possible to use a function named @racket[add] in an infix expression:

@(hackett-interaction
  (def add +)
  (eval:check {1 add 2} 3))

In fact, there is not even any restriction that functions used in infix expressions must be
identifiers. Arbitrary expressions that produce functions may also be used infix:

@(hackett-interaction
  (eval:check {1 (λ [x _] x) 2} 1))

Infix syntax can also be used to chain multiple operators together in the same expression, so the
general syntax of infix mode can be described with the following grammar:

@(racketblock
  @#,BNF-seq[@litchar{@"{"} @nonterm{arg expr}
             @kleeneplus[@BNF-group[@nonterm{function expr} @nonterm{arg expr}]]
             @litchar{@"}"}])

…where each @nonterm{function expr} is known as an @deftech{infix operator}.

@(hackett-examples
  (eval:check {1 + 2 + 3} 6))

Astute readers might notice that operators chained in this way create a minor ambiguity. Is
@racket[{_x _f _y _g _z}] grouped like this?

@(racketblock
  (_g (_f _x _y) _z))

…or like this?

@(racketblock
  (_f _x (_g _y _z)))

Both interpretations are potentially reasonable. For operators like @racket[+], the grouping does not
matter, because @racket[+] is associative, so the result will be the same whichever grouping is
picked. For other operators, however, the grouping is meaningful. For example, @racket[-] can produce
very different results depending on which grouping is picked:

@(hackett-interaction
  (eval:check {{10 - 15} - 6} -11)
  (eval:check {10 - {15 - 6}} 1))

How does Hackett determine which grouping to use? Well, it uses a notion of @deftech{operator fixity}
to decide on a case-by-case basis. Some operators should be grouped the first way (they
“associate left”) while others should be grouped the second way (they “associate right”). The
@racket[-] operator, for example, associates left, while the @racket[::] operator associates right:

@(hackett-interaction
  (eval:check {10 - 15 - 6} -11)
  {1 :: 2 :: 3 :: Nil})

Operator fixity can be specified when a binding is defined by providing a @deftech{fixity annotation},
which is either @racket[#:fixity left] or @racket[#:fixity right]. Using a fixity annotation, it is
possible to write a version of @racket[-] that associates right:

@(hackett-interaction
  (def -/r #:fixity right -)
  (eval:check {10 -/r 15 -/r 6} 1))

If no fixity annotation is specified, the default fixity is @racket[left].

Additionally, infix syntax can be used in types as well as expressions, and it works the same way.
Type constructors may also have @tech{operator fixity}, most notably @racket[t:->], which associates
right. This makes writing type signatures for curried functions much more palatable, since
@racket[{_a t:-> _b t:-> _c}] tends to be easier to visually scan than
@racket[(t:-> _a (t:-> _b _c))], especially when the argument types are long or function types are
nested in argument positions.

@section[#:tag "guide-working-with-data"]{Working with data}

Hackett is a @emph{pure} programming language, which means functions cannot have side-effects. This
makes Hackett functions truly functions in the mathematical sense—the output is always the same for a
given input, and a function’s evaluation cannot do anything but produce a value as output. This
encourages a very @emph{data-oriented} style of programming, assembling pipelines of pure functions
that operate on data structures.

For that reason, the basic building blocks of Hackett are built around producing and consuming data,
and Hackett makes it easy to define new data structures. You’ve already seen integers, but Hackett
provides a myriad of built-in datatypes. This section will cover some of those datatypes, how to
produce and consume them, and how to build your own.

@subsection[#:tag "guide-enumerations"]{Enumerations}

@(define enumerations-eval (make-hackett-eval))

One of the most fundamental sorts of data that can be represented in Hackett are
@italic{enumerations}, often called “enums” in other languages. An enumeration is a type that can be
one of a set of predefined values. For example, the days of the week form an obvious enumeration. We
can define that enumeration in Hackett using the @racket[data] form:

@(hackett-interaction
  #:eval enumerations-eval
  #:no-prompt
  (data Weekday
    sunday monday tuesday wednesday
    thursday friday saturday))

@(enumerations-eval
  '(instance (Show Weekday)
     [show (λ* [[sunday] "sunday"]
               [[monday] "monday"]
               [[tuesday] "tuesday"]
               [[wednesday] "wednesday"]
               [[thursday] "thursday"]
               [[friday] "friday"]
               [[saturday] "saturday"])]))

This declaration defines two things: a @tech{type} and a set of @tech{values}. Specifically, it
defines a new type named @racket[Weekday], and it defines 7 values, @racket[monday] through
@racket[sunday]. You can see that each of these names are bound to values of the @racket[Weekday]
type by evaluating them in the REPL:

@(hackett-interaction
  #:eval enumerations-eval
  monday
  thursday)

Of course, these values are not very interesting on their own. Presumably, once we have an
enumeration, we would like to be able to @emph{do something} with its values. For example, we might
wish to write a function that determines if a weekday is a weekend—that is, if it is @racket[sunday]
or @racket[saturday]. To do this, we need some way to check if a weekday is a particular value.

We can do this by using @italic{pattern matching}, which makes it possible to make a decision based on
the different values of an enumeration. Here’s one way to write our @racket[is-weekend?] function:

@(hackett-interaction
  #:eval enumerations-eval
  (defn is-weekend? : {Weekday t:-> t:Bool}
    [[sunday] True]
    [[monday] False]
    [[tuesday] False]
    [[wednesday] False]
    [[thursday] False]
    [[friday] False]
    [[saturday] True])
  (is-weekend? saturday)
  (is-weekend? wednesday))

This works! Each clause in @racket[defn] provides a @tech{pattern} to match against. If a pattern is
the name of an enumeration value, it only matches if the supplied argument is that specific value.

Sadly, while the above definition works, it’s a little wordy. To simplify it a little, it’s possible
to use the special @racket[_] pattern, which matches @emph{any} value. This can be used to create a
sort of “fallthrough” case:

@(hackett-interaction
  #:eval enumerations-eval
  (defn is-weekend? : {Weekday t:-> t:Bool}
    [[sunday] True]
    [[saturday] True]
    [[_] False])
  (is-weekend? saturday)
  (is-weekend? wednesday))

This works because patterns in @racket[defn] are matched from top to bottom, picking the first one
that successfully matches.

@subsection[#:tag "guide-intro-to-lists"]{An introduction to lists}

While it’s great to be able to represent weekdays with our @racket[Weekday] type, we don’t have any
way to talk about multiple weekdays at a time. To do this, we need a data structure that can hold
multiple values of the same type. One such data structure is a @tech{list}, which represents a
singly-linked list. Lists are @emph{homogenous}, which means they hold a set of values that all have
the same @tech{type}.

A list is built out of two fundamental pieces: the empty list, named @racket[Nil], and the “cons”
constructor, named @racket[::]. These have the following types:

@margin-note{
  The use of @racket[t:forall] in the types of @racket[Nil] and @racket[::] indicates that lists are
  @emph{polymorphic}—that is, they can hold values of any type. This will be covered in more detail
  in a future section.}

@nested[#:style 'inset]{
  @deftogether[
    [@defthing[#:link-target? #f Nil (t:forall [a] (t:List a))]
     @defthing[#:link-target? #f :: (t:forall [a] {a t:-> (t:List a) t:-> (t:List a)})]]]}

Essentially, @racket[::] prepends a single element to an existing list (known as the “tail” of the
list), and @racket[Nil] is the end of every list. To create a single-element list, use @racket[::]
to prepend an element to the empty list:

@(hackett-interaction
  {1 :: Nil})

A list of more elements can be created with nested uses of @racket[::]:

@(hackett-interaction
  {1 :: {2 :: {3 :: Nil}}})

Additionally, @racket[::] is an @tech{infix operator} that associates right, so nested braces can be
elided when constructing lists:

@(hackett-interaction
  {1 :: 2 :: 3 :: Nil})

Once we have a list, we can do various things with it. For example, we can concatenate two lists
together using the @racket[++] operator:

@(hackett-interaction
  {{1 :: 2 :: Nil} ++ {3 :: 4 :: Nil}})

We can sum a list of numbers using the @racket[sum] function:

@(hackett-interaction
  (eval:check (sum {1 :: 2 :: 3 :: Nil}) 6))

We can even apply a function to each element of a list to produce a new list by using the @racket[map]
function:

@(hackett-interaction
  (map (+ 1) {1 :: 2 :: 3 :: Nil}))

Combining this with our @racket[Weekday] type from earlier, we can create a list of all the days in
the week:

@(hackett-interaction
  #:eval enumerations-eval
  (def weekdays : (List Weekday)
    {sunday :: monday :: tuesday :: wednesday
     :: thursday :: friday :: saturday :: Nil}))

The @racket[filter] allows selecting elements from a list that match a given predicate. Using
@racket[filter] combined with the @racket[is-weekend?] function we wrote earlier, it’s possible to
produce a list that contains only weekends:

@(hackett-interaction
  #:eval enumerations-eval
  (filter is-weekend? weekdays))

@subsection[#:tag "guide-intro-to-maybe"]{Representing operations that can fail}

While it’s interesting that we can construct lists and iterate over them, it’s important to be able to
@emph{consume} lists as well. In many languages, there are functions to access the first element of a
list, and Hackett has such a function, too, called @racket[head]. However, @racket[head] is an
interesting operation, since it can @emph{fail}. What happens if we try to get the first element of
an empty list?

@(hackett-interaction
  (eval:check (head (: Nil (t:List t:Integer))) (: Nothing (t:Maybe t:Integer))))

Rather than produce an error, Hackett returns @racket[Nothing]. At first, this might seem like
@tt{null} or @tt{nil} in other languages, but it isn’t—in those languages, almost @emph{anything} has
the potential to be @tt{null}, so it’s easy to accidentally forget to properly handle @tt{null} cases.
In Hackett, @racket[Nothing] is just an ordinary value of type @racket[(t:Maybe _a)].

To see why this is different, let’s apply @racket[head] to a list that actually does contain some
elements:

@(hackett-interaction
  (eval:check (head {1 :: 2 :: 3 :: Nil}) (Just 1)))

Note that it is wrapped in @racket[Just]. This is because the @racket[t:Maybe] type is a wrapper that
encodes the notion that the value might not be there. If it is, it is wrapped in @racket[Just]. If it
isn’t, it’s the plain value @racket[Nothing].

Many Hackett functions produce @racket[t:Maybe]-wrapped values, since there are many operations that
have the potential to fail. Importantly, this is always expressed in the function’s type:

@(hackett-interaction
  (#:type head)
  (#:type tail))

@margin-note{
  While this is generally true—the majority of Hackett functions express failure potential at the type
  level—this is not @emph{guaranteed} by the typechecker. For more information on the ways functions
  can fail at runtime, see @secref["guide-bottoms"].}

Since @racket[t:Maybe] is explicitly annotated in the return type (rather than always implicitly
possible, like @tt{null} in many other languages), you can know exactly which functions can fail, and
the typechecker will ensure you properly handle the failure case.

Of course, while this is very nice, it’s not completely useful to get back a value of type
@racket[(t:Maybe t:Integer)] if we really need an @racket[t:Integer], since the two are entirely
different types. We cannot, for example, add an @racket[t:Integer] to a @racket[(t:Maybe t:Integer)]:

@(hackett-interaction
  (eval:error {1 + (Just 2)}))

So, at some point, we need to have @emph{some} way to unwrap the @racket[t:Maybe] wrapper. One way to
do this is using the @racket[from-maybe] function:

@(hackett-interaction
  (#:type from-maybe))

Note that this function is @emph{not} @racket[(t:forall [a] {(t:Maybe a) t:-> a})]! Such a function
would entirely defeat the purpose of using @racket[t:Maybe] to indicate failure, since it would not
have any way to properly handle the @racket[Nothing] case. Instead, @racket[from-maybe] requires that
you specify a default value to produce in the event that the second argument is @racket[Nothing]:

@(hackett-interaction
  (eval:check (from-maybe 0 (Just 42)) 42)
  (eval:check (from-maybe 0 (: Nothing (t:Maybe t:Integer))) 0))

However, this is not always the right thing to do. Sometimes, a default value might not make any
sense. Sometimes, a failure is something that needs to be handled at a different level, not
immediately, but you might still want to modify the value inside a @racket[Just] wrapper. To do this,
it’s actually possible to use the @racket[map] function to modify the value inside @racket[Just], in
the same way that it’s possible to modify the values inside a list:

@(hackett-interaction
  (eval:check (map (+ 1) (Just 11)) (Just 12))
  (eval:check (map (+ 1) (: Nothing (t:Maybe t:Integer))) (: Nothing (t:Maybe t:Integer))))

If this is confusing to you, you can think of @racket[t:Maybe] as a special case of @racket[t:List]:
while a value of type @racket[(t:List _a)] can hold @emph{any number} of @racket[_a]s, a value of type
@racket[(t:Maybe _a)] can hold @emph{exactly zero or one} @racket[_a]. Using the @racket[map] function
on a value wrapped in @racket[Just] is therefore sort of like mapping over a single-element list, and
using it on @racket[Nothing] is like mapping over the empty list.

@(close-eval enumerations-eval)

@section[#:tag "guide-bottoms"]{Partial Functions and Nontermination}

In Hackett, functions are generally expected to be @deftech[#:key "total function"]{total}, which
means they should produce a result for all possible inputs. For example, @racket[not] is obviously
defined for both @racket[True] and @racket[False], which are the only possible values of the
@racket[t:Bool] type. Total functions allow a programmer to reason about programs using the types
alone; a function with the type @racket[{A t:-> B}] implies that is is always possible to get a
@racket[B] when you have an @racket[A].

@see-reference-note["reference-controlling-evaluation"]{partial functions}

Sometimes, however, this is impractical. Sometimes the type system is not expressive enough to
constrain the input type as much as the programmer would like. In other cases, the burden of assigning
a precise type to a value might be too high. In these situations, Hackett allows the programmer to
define @deftech{partial functions}. Partial functions should be used extremely judiciously—when a
partial function is evaluated at runtime, the program will @emph{crash}, producing an error message.

Hackett provides a built-in partial function named @racket[error!] for signaling unrecoverable errors.
This function is not only partial, it is actually undefined for @emph{all} possible values! This
partiality can be observed in @racket[error!]’s type:

@(hackett-interaction
  (#:type error!))

The @racket[error!] function seems impossible, since it promises to produce @emph{anything}, of any
type, when given nothing but a string. Indeed, this type signature lies; it promises it will produce
anything, but this is only possible because it will never actually return anything. When
@racket[error!]’s result is needed, the program will simply crash.

@(hackett-interaction
  #:no-preserve-source-locations
  (eval:error (: (error! "urk!") t:Unit)))

Partial functions in Hackett are idiomatically indicated by including a @litchar{!} symbol at the end
of their names, but this is only a convention; it is not enforced by the compiler or typechecker.

The @racket[error!] function can be considered a way to subvert the type system. Its primary purpose
is to provide a programmer the ability to mark cases which are “impossible” based on the logic of the
program, but the typechecker cannot determine that is true. Of course, in practice, things that where
once truly impossible may eventually become possible as code changes, so using some other notion of
failure (such as returning a value wrapped in @racket[t:Maybe]) is generally preferred whenever
possible.

In addition to @racket[error!], another partial value provided by Hackett is @racket[undefined!]. This
is a value, not a function, and it miraculously has any type. The @racket[undefined!] value will crash
the program as soon as it is evaluated, but it is often useful for getting something to typecheck
before you have finished implementing all of the cases. Generally, @racket[undefined!] can be useful
as a tool while iteratively writing code, but all uses of @racket[undefined!] should be replaced by
“real” implementations before the code is considered complete.

Interestingly, while @racket[error!] and @racket[undefined!] crash the program, it is not impossible
to write a functions with the same type signatures, but which do @emph{not} crash the program. How?
Well, it’s true that a function that promises to return a value of any type the caller asks for can
never return, but there is another possibility besides halting: the function can simply infinitely
loop. Here is an example of such a function, called @racket[diverge!]:

@(racketblock
  (defn diverge! : (t:forall [a] {t:String t:-> a})
    [[x] (diverge! x)]))

This sort of function is often @emph{also} considered partial, since it does not return a value for
all of its inputs.

It’s important to keep in mind that Hackett is lazy, and use of partial functions does not change
that! This can result in curious behavior, where a partial function does not cause a program to halt
or diverge, simply because it isn’t evaluated:

@(hackett-interaction
  (const Unit (error! "never gets here")))

In fact, a partial function can “lurk” in an unevaluated thunk for quite a long time, but forcing its
evaluation will cause its effects to become visible. These unpredictable effects are another reason to
use partial functions extremely sparingly.

Partial values that, once evaluated, will trigger partial behavior are known as @deftech{bottoms}.
Documentation of certain forms and functions may note that something is true “ignoring bottom”. This
is because many guarantees can technically be broken when partial functions are involved, but it is
often more useful to temporarily pretend they do not exist in order to reason about some code using
types alone. This is a powerful property of Hackett’s type system; do not squander that power with
reckless use of partiality.
