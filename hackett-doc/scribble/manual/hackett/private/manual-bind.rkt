; The contents of this module include a partial copy of the implementation of ‘defform’ from
; scribble/private/manual-bind, tweaked to support rendering different symbolic names in place of the
; actual names of documented bindings. This is necessary to allow Hackett to properly document types,
; which are prefixed with ‘#%hackett-type:’, a mangling scheme that should not appear in the
; documentation.
;
; The contents of this module are dual-licensed under the compatible ISC and MIT licenses, the former
; being the license of the entire Hackett project, the latter the license of the Racket distribution.
; The full text of the original license is reproduced below:
;
; Copyright 2017 PLT Design
;
; Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
; associated documentation files (the "Software"), to deal in the Software without restriction,
; including without limitation the rights to use, copy, modify, merge, publish, distribute,
; sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
; furnished to do so, subject to the following conditions:
;
; The above copyright notice and this permission notice shall be included in all copies or substantial
; portions of the Software.
;
; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
; NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES
; OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
; CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
#lang racket/base

(require scribble/struct
         scribble/racket
         scribble/basic
         scribble/manual-struct
         scribble/private/qsloc
         scribble/private/manual-utils
         scribble/private/manual-vars
         scribble/private/manual-scheme
         scribble/private/manual-bind
         racket/list
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     syntax/parse/experimental/template)
         (for-label racket/base))

(provide defform defform* defidform
         (for-syntax kind-kw id-kw display-id-kw link-target?-kw
                     literals-kw contracts-kw grammar subs-kw))

(begin-for-syntax
 (define-splicing-syntax-class kind-kw
   #:description "#:kind keyword"
   (pattern (~seq #:kind kind))
   (pattern (~seq)
            #:with kind #'#f))

 (define-splicing-syntax-class id-kw
   #:description "#:id keyword"
   (pattern {~optional {~seq #:id defined-id:id}}))

 (define-splicing-syntax-class display-id-kw
   #:description "#:display-id keyword"
   (pattern {~optional {~seq #:display-id display-id:id}}))

 (define-splicing-syntax-class link-target?-kw
   #:description "#:link-target? keyword"
   (pattern (~seq #:link-target? expr))
   (pattern (~seq)
            #:with expr #'#t))

 (define-splicing-syntax-class literals-kw
   #:description "#:literals keyword"
   (pattern (~seq #:literals (lit:id ...)))
   (pattern (~seq)
            #:with (lit ...) #'()))

 (define-splicing-syntax-class contracts-kw
   #:description "#:contracts keyword"
   (pattern (~seq #:contracts (~and cs ([contract-nonterm:id contract-expr] ...))))
   (pattern (~seq)
            #:with (~and cs ((contract-nonterm contract-expr) ...)) #'()))

 (define-syntax-class grammar
   #:description "grammar"
   (pattern ([non-term-id:id non-term-form ...+] ...)))

 (define-splicing-syntax-class subs-kw
   #:description "#:grammar keyword"
   #:attributes (g (g.non-term-id 1) (g.non-term-form 2))
   (pattern (~seq #:grammar g:grammar))
   (pattern (~seq) #:with g:grammar #'())))

(define-syntax (defform*/subs stx)
  (syntax-parse stx
    [(_ k:kind-kw lt:link-target?-kw d:id-kw d*:display-id-kw l:literals-kw [spec spec1 ...]
        g:grammar
        c:contracts-kw
        desc ...)
     (with-syntax* ([defined-id (if (attribute d.defined-id)
                                    #'d.defined-id
                                    (syntax-case #'spec ()
                                      [(spec-id . _) #'spec-id]))]
                    [display-id (if (attribute d*.display-id)
                                    #'d*.display-id
                                    (syntax-case #'spec ()
                                      [(spec-id . _) #'spec-id]))]
                    [(new-spec ...)
                     (for/list ([spec (in-list (syntax->list #'(spec spec1 ...)))])
                       (let loop ([spec spec])
                         (if (and (identifier? spec)
                                  (free-identifier=? spec #'display-id))
                             (datum->syntax #'here '(unsyntax x) spec spec)
                             (syntax-case spec ()
                               [(a . b)
                                (datum->syntax spec
                                               (cons (loop #'a) (loop #'b))
                                               spec
                                               spec)]
                               [_ spec]))))])
       #'(with-togetherable-racket-variables
            (l.lit ...)
            ([form [display-id spec]] [form [display-id spec1]] ...
             [non-term (g.non-term-id g.non-term-form ...)] ...)
            (*defforms k.kind lt.expr (quote-syntax defined-id) (quote-syntax display-id)
                       '(spec spec1 ...)
                       (list (lambda (x) (racketblock0/form new-spec)) ...)
                       '((g.non-term-id g.non-term-form ...) ...)
                       (list (list (lambda () (racket g.non-term-id))
                                   (lambda () (racketblock0/form g.non-term-form))
                                   ...)
                             ...)
                       (list (list (lambda () (racket c.contract-nonterm))
                                   (lambda () (racketblock0 c.contract-expr)))
                             ...)
                       (lambda () (list desc ...)))))]))

(define-syntax (defform* stx)
  (syntax-parse stx
    [(_ k:kind-kw lt:link-target?-kw d:id-kw d*:display-id-kw l:literals-kw [spec ...]
        subs:subs-kw c:contracts-kw desc ...)
     (template/loc stx
       (defform*/subs #:kind k.kind 
         #:link-target? lt.expr
         {?? {?@ . d}} {?? {?@ . d*}}
         #:literals (l.lit ...)
         [spec ...] subs.g #:contracts c.cs desc ...))]))

(define-syntax (defform stx)
  (syntax-parse stx
    [(_ k:kind-kw lt:link-target?-kw d:id-kw d*:display-id-kw l:literals-kw spec
        subs:subs-kw c:contracts-kw desc ...)
     (template/loc stx
       (defform*/subs #:kind k.kind
         #:link-target? lt.expr
         {?? {?@ . d}} {?? {?@ . d*}}
         #:literals (l.lit ...)
         [spec] subs.g #:contracts c.cs desc ...))]))

(define-syntax (defidform stx)
  (syntax-parse stx
    [(_ k:kind-kw lt:link-target?-kw d:id-kw spec-id desc ...)
     (template
      (with-togetherable-racket-variables
        ()
        ()
        (*defforms k.kind lt.expr
                   (quote-syntax/loc {?? d.defined-id spec-id}) (quote-syntax/loc spec-id)
                   '(spec-id)
                   (list (lambda (x) (make-omitable-paragraph (list x))))
                   null
                   null
                   null
                   (lambda () (list desc ...)))))]))

(define (defform-site defined-id display-id)
  (let ([target-maker (id-to-form-target-maker defined-id #t)]
        [content (to-element display-id #:defn? #t)]
        [ref-content (to-element display-id)])
    (target-maker
     content
     (lambda (tag)
       (make-toc-target2-element
        #f
        (if display-id
            (make-index-element
             #f content tag
             (list (datum-intern-literal (symbol->string (syntax-e display-id))))
             (list ref-content)
             (with-exporting-libraries
                 (lambda (libs)
                   (make-form-index-desc (syntax-e display-id)
                                         libs))))
            content)
        tag
        ref-content)))))

(define (*defforms kind link? defined-id display-id forms form-procs subs sub-procs contract-procs
                   content-thunk)
  (parameterize ([current-meta-list '(... ...+)])
    (make-box-splice
     (cons
      (make-blockquote
       vertical-inset-style
       (list
        (make-table
         boxed-style
         (append
          (for/list ([form (in-list forms)]
                     [form-proc (in-list form-procs)]
                     [i (in-naturals)])
            (list
             ((if (zero? i) (add-background-label (or kind "syntax")) values)
              (list
               ((or form-proc
                    (lambda (x)
                      (make-omitable-paragraph
                       (list (to-element `(,x . ,(cdr form)))))))
                (and display-id
                     (if (and (eq? form (car forms))
                              defined-id
                              link?)
                         (defform-site defined-id display-id)
                         (to-element #:defn? #t display-id))))))))
          (if (null? sub-procs)
              null
              (list (list flow-empty-line)
                    (list (make-flow
                           (list (let ([l (map (lambda (sub)
                                                 (map (lambda (f) (f)) sub))
                                               sub-procs)])
                                   (*racketrawgrammars "specgrammar"
                                                       (map car l)
                                                       (map cdr l))))))))
          (make-contracts-table contract-procs)))))
      (content-thunk)))))

(define (*racketrawgrammars style nonterms clauseses)
  (make-table
   `((valignment baseline baseline baseline baseline baseline)
     (alignment right left center left left)
     (style ,style))
   (cdr
    (append-map
     (lambda (nonterm clauses)
       (list*
        (list flow-empty-line flow-empty-line flow-empty-line
              flow-empty-line flow-empty-line)
        (list (to-flow nonterm) flow-empty-line (to-flow "=") flow-empty-line
              (make-flow (list (car clauses))))
        (map (lambda (clause)
               (list flow-empty-line flow-empty-line
                     (to-flow "|") flow-empty-line
                     (make-flow (list clause))))
             (cdr clauses))))
     nonterms clauseses))))

(define (make-contracts-table contract-procs)
  (if (null? contract-procs)
      null
      (append
       (list (list flow-empty-line))
       (list (list (make-flow
                    (map (lambda (c)
                           (make-table
                            "argcontract"
                            (list
                             (list (to-flow (hspace 2))
                                   (to-flow ((car c)))
                                   flow-spacer
                                   (to-flow ":")
                                   flow-spacer
                                   (make-flow (list ((cadr c))))))))
                         contract-procs)))))))
