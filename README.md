# Hackett [![Build Status](https://travis-ci.org/lexi-lambda/hackett.svg?branch=master)](https://travis-ci.org/lexi-lambda/hackett)

Hackett is an attempt to implement a Haskell-like language with support for Racket’s macro system, built using the techniques described in the paper [*Type Systems as Macros*][types-as-macros]. It is currently *extremely* work-in-progress.

Here are some of the features that Hackett supports **right now**:

  - Bidirectional type inference
  - Algebraic datatypes (ADTs)
  - Pattern matching
  - Exhaustiveness checking
  - Typeclasses
  - Higher-kinded types
  - Higher-rank polymorphism
  - Type-aware/type-directed macros
  - Laziness
  - Syntax for infix operators

Here are some of the features that still need to be implemented for a minimal release:

  - Default class methods
  - Scoped type variables
  - Kindchecking
  - Type expanders (of which type aliases are a subset)

And finally, here is a (non-exhaustive) collection of features I would like to eventually support:

  - Multi-parameter typeclasses
  - Functional dependencies
  - GADTs
  - Row types
  - Type families

Due to the way Hackett is implemented, many things that are language features in Haskell can be derived concepts in Hackett. In fact, Hackett’s ADTs are not primitives, they are actually implemented as a library via the `data` and `case` macros in `hackett/private/adt`. Other things, like newtype deriving and generics, should be possible to implement as derived concepts as well.

Here’s some sample Hackett code that demonstrates some of Hackett’s features:

```racket
#lang hackett

(data (Maybe a)
  nothing
  (just a))

(def x : Integer
  (let ([y 3]
        [z 7])
    {y + z}))

(class (Show a)
  [show : {a -> String}])

(instance (forall [a] (Show a) => (Show (Maybe a)))
  [show (λ* [[(just x)] {"(just " ++ (show x) ++ ")"}]
            [[nothing ] "nothing"])])
```

[**For a much more in-depth look at Hackett, see the documentation.**][hackett-docs]

## Trying Hackett

To reiterate: **Hackett is extremely experimental right now.** Things are not guaranteed to work correctly (or work at all), and things are likely to change dramatically. If you really want to install Hackett to play around with it, though, you can.

You will need to have Racket installed to use Hackett. Using `raco`, you can install Hackett as a package:

```
$ raco pkg install hackett
```

Now you can use Hackett by writing `#lang hackett` at the top of a file.

[hackett-docs]: https://pkg-build.racket-lang.org/doc/hackett@hackett-doc/
[types-as-macros]: http://www.ccs.neu.edu/home/stchang/pubs/ckg-popl2017.pdf
