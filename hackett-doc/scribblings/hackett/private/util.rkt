#lang at-exp racket/base

(require (for-label hackett
                    hackett/data/identity
                    hackett/monad/error
                    hackett/monad/reader
                    hackett/monad/trans)

         (for-syntax racket/base)

         racket/sandbox
         scribble/core
         scribble/example
         scribble/html-properties
         (except-in scribble/manual defclass defmethod)
         scribble/manual/hackett
         setup/collects
         syntax/parse/define)

(provide (for-label (all-from-out hackett)
                    (all-from-out hackett/data/identity)
                    (all-from-out hackett/monad/error)
                    (all-from-out hackett/monad/reader)
                    (all-from-out hackett/monad/trans))
         (all-from-out scribble/manual/hackett)
         close-eval

         make-hackett-eval hackett-examples hackett-interaction

         tech/racket-reference

         other-reference-note see-guide-note later-guide-note see-reference-note)

;; ---------------------------------------------------------------------------------------------------
;; evaluation

(define (make-hackett-eval)
  (make-base-eval #:lang 'hackett '(require hackett/data/identity
                                            hackett/monad/error
                                            hackett/monad/reader
                                            hackett/monad/trans
                                            (only-in hackett/private/prim unsafe-run-io!))))

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

;; ---------------------------------------------------------------------------------------------------
;; internal references

(define css-resource
  (make-css-addition
   (path->collects-relative
    (collection-file-path "other-reference.css" "scribblings" "hackett" "private"))))

(define finger (element (style "margin-note__image-left margin-note__image-left--finger"
                               (list css-resource))
                        '()))

(define (flexible-container . content)
  (element (style "flexible-container" (list css-resource (alt-tag "div"))) content))
(define (flexible-element . content)
  (element (style "flexible-element" (list css-resource (alt-tag "div"))) content))

(define (other-reference-note . pre-content)
  (margin-note (flexible-container finger (apply flexible-element pre-content))))

(define (see-guide-note tag . pre-content)
  @other-reference-note{
    @Secref[tag] in @secref["guide"] has additional examples of @|pre-content|.})

(define (later-guide-note tag . pre-content)
  @other-reference-note{
    @secref[tag] (later in this guide) explains more about @|pre-content|.})

(define (see-reference-note tag . pre-content)
  @other-reference-note{
    @Secref[tag] in @secref["reference"] has additional information on @|pre-content|.})
