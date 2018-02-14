#lang hackett

(require hackett/private/test)

(test {(if True
           Unit
           (case (error! "should never get here")
             [Unit Unit]))
       ==! Unit})
