#lang scribble/manual

@(require scribble/core
          scribblings/hackett/private/util)

@title{The Hackett Programming Language}
@author{@author+email["Alexis King" "lexi.lambda@gmail.com"]}
@defmodule[hackett #:lang]

@(define (yellow . content)
   (make-element (make-style #f (list (make-background-color-property "yellow"))) content))

@nested[#:style 'inset]{
  @yellow{@bold{WARNING}}: The contents of this manual are considered @emph{unstable, experimental,
  and subject to change}; compatibility will not be maintained.}

@emph{Hackett} is a statically typed, pure, lazy, functional programming language in the Racket
language ecosystem. Despite significant differences from @hash-lang[] @racketmodname[racket], Hackett
shares its S-expression syntax and powerful, hygienic macro system. Unlike Typed Racket, Hackett is
@emph{not} gradually typed—it is designed with typed programs in mind, and it does not have any
dynamically-typed counterpart.

This manual is divided into two parts: @secref["guide"], which provides a gentler, tutorial-style
overview of Hackett’s language features, and @secref["reference"], a precise and authorative
specification of the language and all of the forms and functions provided in the standard library.

For those new to Hackett, even those already familiar with languages similar to Hackett, like Racket
or Haskell, it is highly recommended you start with @secref["guide"]. For the precise details of
various language features, @secref["reference"] may be more appropriate. However, neither is intended
to be read from beginning to end, in order: both sections are indexed and searchable as well as
internally cross-referenced, and links are provided in the margins to jump to corresponding companion
sections, when available.

@table-of-contents[]

@include-section["guide.scrbl"]
@include-section["reference.scrbl"]

@index-section[]
