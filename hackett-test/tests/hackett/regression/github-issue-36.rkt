#lang hackett

(require hackett/private/test)

(test {(show (tuple 1 2)) ==! "(tuple 1 2)"})
