#lang hackett

(require hackett/private/test)

(test {(show (Tuple 1 "str")) ==! "(Tuple 1 \"str\")"})
