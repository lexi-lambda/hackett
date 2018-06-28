#lang at-exp racket/base

(require (for-label hackett
                    hackett/data/identity
                    hackett/monad/base
                    hackett/monad/error
                    hackett/monad/reader
                    hackett/monad/trans)

         (for-syntax racket/base
                     racket/list
                     racket/match
                     racket/require-transform)

         scribble/core
         scribble/example
         scribble/html-properties
         (except-in scribble/manual defclass defmethod)
         scribble/manual/hackett
         scribble/racket
         setup/collects
         syntax/parse/define)

(provide (for-label (all-from-out hackett)
                    (all-from-out hackett/data/identity)
                    (all-from-out hackett/monad/base)
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
  (let ([hackett-eval (make-base-eval #:lang 'hackett)])
    (hackett-eval '(require hackett
                            hackett/data/identity
                            hackett/monad/base
                            hackett/monad/error
                            hackett/monad/reader
                            hackett/monad/trans
                            (only-in hackett/private/prim unsafe-run-io!)))
    hackett-eval))

(begin-for-syntax
  (define (do-expand-eval-transformers stx)
    (syntax-rearm
     (syntax-parse (syntax-disarm stx (current-code-inspector))
       [x:type-binding-id
        #:do [(define bare-id #'x.bare-id)]
        (datum->syntax bare-id (syntax-e bare-id) #'x)]
       [(a . b)
        (datum->syntax this-syntax
                       (cons (do-expand-eval-transformers #'a)
                             (do-expand-eval-transformers #'b))
                       this-syntax
                       this-syntax)]
       [_ this-syntax])
     stx))

  (define (expand-eval-transformers stx)
    (syntax-parse stx
      #:datum-literals [eval:alts eval:check]
      [(eval:alts . _)
       stx]
      [(eval:check eval expect)
       #`(eval:alts eval (eval:check #,(do-expand-eval-transformers #'eval)
                                     #,(do-expand-eval-transformers #'expect)))]
      [_
       #`(eval:alts #,stx #,(do-expand-eval-transformers stx))])))

(define-syntax-parser hackett-examples
  [(_ {~or {~optional {~seq #:eval eval:expr}}
           {~optional {~and #:once once}}
           {~optional {~seq #:label label:expr}}
           {~optional {~and #:no-preserve-source-locations no-preserve-source-locations}}
           {~optional {~and #:no-prompt no-prompt}}}
      ... body ...)
   #:with eval* (or (attribute eval) #'(make-hackett-eval))
   #:with [once* ...] (cond [(attribute once) #'[once]]
                            [(attribute eval) #'[]]
                            [else             #'[#:once]])
   #:with [preserve-source-locations ...] (if (attribute no-preserve-source-locations) #'[]
                                              #'[#:preserve-source-locations])
   #:with [body* ...] (map expand-eval-transformers (attribute body))
   (syntax/loc this-syntax
     (examples
      #:eval eval*
      preserve-source-locations ...
      once* ...
      {~? {~@ #:label label}}
      {~? no-prompt}
      body* ...))])

(define-syntax-parser hackett-interaction
  [(_ body ...)
   (syntax/loc this-syntax
     (hackett-examples #:label #f body ...))])

;; ---------------------------------------------------------------------------------------------------
;; cross-manual references

(define (tech/racket-reference #:key [key #f] #:normalize? [normalize? #t] . pre-content)
  (apply tech #:doc '(lib "scribblings/reference/reference.scrbl")
         #:key key #:normalize? normalize? pre-content))

;; ---------------------------------------------------------------------------------------------------
;; type bindings

(define-syntax prefix+provide-hackett-types
  (make-require-transformer
   (syntax-parser
     [(_ require-spec ...)
      (define-values [imports import-sources] (expand-import #'(for-label require-spec ...)))
      (values (append*
               (filter
                values
                (for/list ([i (in-list imports)])
                  (match i
                    [(import (and local-id (app (λ (id) (symbol->string (syntax-e id)))
                                                (regexp #px"^#%hackett-type:(.+)$"
                                                        (list _ (and (not #f) bare-str)))))
                             src-sym src-mod-path mode req-mode orig-mode orig-stx)
                     (let* ([bare-sym (string->symbol bare-str)]
                            [bare-id ((make-syntax-introducer #t)
                                      (datum->syntax #f bare-sym local-id local-id))]
                            [prefixed-sym (string->symbol (string-append "t:" bare-str))]
                            [prefixed-id (datum->syntax local-id prefixed-sym local-id local-id)])
                       (syntax-local-lift-module-end-declaration
                        #`(define+provide-hackett-type-binding #,bare-id #,prefixed-id #,local-id))
                       (list
                        i
                        (import bare-id src-sym src-mod-path mode req-mode orig-mode orig-stx)))]
                    [_ #f]))))
              import-sources)])))

(define-simple-macro (define+provide-hackett-type-binding bare-id:id prefixed-id:id orig-id:id)
  (begin
    (define-syntax prefixed-id
      (make-element-id-transformer
       (λ (stx) #`(racket #,(datum->syntax (quote-syntax bare-id)
                                           (syntax-e (quote-syntax bare-id))
                                           stx)))))
    (begin-for-syntax
      (register-type-binding!
       (quote-syntax prefixed-id)
       (quote-syntax orig-id)
       (quote-syntax bare-id)))
    (provide prefixed-id)))

(require (prefix+provide-hackett-types hackett
                                       hackett/data/identity
                                       hackett/monad/base
                                       hackett/monad/error
                                       hackett/monad/reader
                                       hackett/monad/trans))

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
    @Secref[tag] (later in this guide) explains more about @|pre-content|.})

(define (see-reference-note tag . pre-content)
  @other-reference-note{
    @Secref[tag] in @secref["reference"] has additional information on @|pre-content|.})
