#lang hackett

(require hackett/private/test)

(test {(show (tuple 1 "str")) ==! "(tuple 1 \"str\")"})
