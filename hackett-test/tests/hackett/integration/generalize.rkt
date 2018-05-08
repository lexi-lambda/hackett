#lang hackett

(require hackett/private/test)

(def identity (λ [x] x))

(test {(identity 42) ==! 42})
(test {(identity "hello") ==! "hello"})
