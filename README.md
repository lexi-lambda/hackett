# higher-rank

A Racket implementation of [Complete and Easy Bidirectional Typechecking
for Higher-Rank Polymorphism][complete-and-easy] using the techniques outlined in [Type Systems as Macros][types-as-macros]. This is a sister project to [the simpler Haskell implementation][haskell-higher-rank] from which it is adapted.

This project should be installed as a Racket package, and it defines `#lang higher-rank`. You can run a REPL from within DrRacket, or you can use the command line:

```
$ cd racket-higher-rank
$ raco pkg install
$ racket -iI higher-rank
Welcome to Racket v6.8.0.3.
> unit
: Unit
#<unit>
> (lambda x x)
: (-> g1^ g1^)
#<procedure:...er-rank/main.rkt:70:18>
> ((: (lambda id ((id (lambda x x)) (id unit)))
      (-> (forall a (-> a a)) Unit))
   (lambda x x))
: Unit
#<unit>
```

[complete-and-easy]: http://www.cs.cmu.edu/~joshuad/papers/bidir/
[types-as-macros]: http://www.ccs.neu.edu/home/stchang/popl2017/
[haskell-higher-rank]: https://github.com/lexi-lambda/higher-rank
