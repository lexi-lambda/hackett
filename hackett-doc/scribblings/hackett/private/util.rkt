#lang racket/base

(require (for-label hackett)

         (for-syntax racket/base)

         racket/sandbox
         scribble/example
         scribble/manual
         scribble/manual/hackett
         syntax/parse/define)

(provide (for-label (all-from-out hackett))
         (all-from-out scribble/manual/hackett)
         close-eval

         make-hackett-eval hackett-examples hackett-interaction

         tech/racket-reference)

;; ---------------------------------------------------------------------------------------------------
;; evaluation

(define (make-hackett-eval)
  (parameterize ([sandbox-output 'string]
                 [sandbox-error-output 'string])
    ; Evaluators produced by racket/sandbox do not automatically require the configure-runtime
    ; submodule of the specified language, so we need to load it explicitly in order to set up the
    ; custom printer.
    (make-evaluator 'hackett #:requires '((submod hackett configure-runtime)))))

(define-simple-macro (hackett-examples
                      {~or {~optional {~seq #:eval eval:expr}}
                           {~optional {~and #:once once}}
                           {~optional {~seq #:label label:expr}}
                           {~optional {~and #:no-preserve-source-locations
                                            no-preserve-source-locations}}}
                      ...
                      body ...)
  #:with eval* (or (attribute eval) #'(make-hackett-eval))
  #:with [once* ...] (cond [(attribute once) #'[once]]
                           [(attribute eval) #'[]]
                           [else             #'[#:once]])
  #:with [label* ...] (if (attribute label) #'[#:label label] #'[])
  #:with [preserve-source-locations ...] (if (attribute no-preserve-source-locations) #'[]
                                             #'[#:preserve-source-locations])
  (examples
   #:eval eval*
   preserve-source-locations ...
   once* ...
   label* ...
   body ...))

(define-simple-macro (hackett-interaction body ...)
  (hackett-examples #:label #f body ...))

;; ---------------------------------------------------------------------------------------------------
;; cross-manual references

(define (tech/racket-reference #:key [key #f] #:normalize? [normalize? #t] . pre-content)
  (apply tech #:doc '(lib "scribblings/reference/reference.scrbl")
         #:key key #:normalize? normalize? pre-content))
