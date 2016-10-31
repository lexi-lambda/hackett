#lang rascal/base

(require rascal/private/prim)

(provide (class Semigroup)
         (rename [append <>]))

(class (Semigroup a)
  [append : {a -> {a -> a}}])

(instance (Semigroup String)
  [append append/String])
