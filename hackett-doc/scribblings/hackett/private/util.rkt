#lang racket/base

(require (for-label hackett)

         (for-syntax racket/base)

         racket/sandbox
         scribble/example
         scribble/manual/hackett
         syntax/parse/define)

(provide (for-label (all-from-out hackett))
         (all-from-out scribble/manual/hackett)
         close-eval

         make-hackett-eval hackett-examples hackett-interaction)

(define (make-hackett-eval [body '()])
  (parameterize ([sandbox-output 'string]
                 [sandbox-error-output 'string])
    (make-module-evaluator
     #:language 'hackett
     `(module m hackett
        ,@body))))

(define-simple-macro (hackett-examples
                      {~or {~optional {~seq #:eval eval:expr}}
                           {~optional {~and #:once once}}
                           {~optional {~seq #:label label:expr}}}
                      ...
                      body ...)
  #:with eval* (or (attribute eval) #'(make-hackett-eval))
  #:with [once* ...] (cond [(attribute once) #'[once]]
                           [(attribute eval) #'[]]
                           [else             #'[#:once]])
  #:with [label* ...] (if (attribute label) #'[#:label label] #'[])
  (examples
   #:eval eval*
   once* ...
   label* ...
   body ...))

(define-simple-macro (hackett-interaction body ...)
  (hackett-examples #:label #f body ...))
