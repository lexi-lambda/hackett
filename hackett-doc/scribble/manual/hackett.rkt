#lang racket/base

(require hackett/private/type-reqprov

         (for-label hackett
                    (only-in (unmangle-types-in #:no-introduce (only-types-in hackett)) => ->))

         (for-syntax racket/base
                     racket/contract
                     racket/list
                     syntax/id-table)

         racket/list
         scribble/struct
         scribble/scheme
         scribble/manual-struct
         scribble/manual
         scribble/decode
         scribble/html-properties
         syntax/parse/define

         (only-in scribble/core make-style make-table-columns nested-flow content?)
         (only-in scribble/private/manual-vars add-background-label)
         (only-in scribble/private/manual-bind
                  id-to-target-maker with-exporting-libraries
                  definition-site)

         (only-meta-in 1 hackett/private/adt)

         (prefix-in patched/ scribble/manual/hackett/private/manual-bind))

(provide (for-syntax register-type-binding! type-binding-value type-binding-id)
         |.| \|\| deftycon deftycon* deftype defdata defclass defmethod)

; Provide an element transformer to typeset |.| (the function composition operator) without vertical
; bars.
(define-syntax |.|
  (make-element-id-transformer
   (λ (stx) #'(racketlink |.| (racketidfont ".")))))

; Provide an element transformer to typeset || (the boolean OR operator) without backslash escapes.
(define-syntax \|\|
  (make-element-id-transformer
   (λ (stx) #'(racketlink \|\| (racketidfont "||")))))

(begin-for-syntax
  (struct type-binding (prefixed-id bare-id)
    #:transparent)

  (define type-label-bindings (make-free-id-table))
  (define/contract (register-type-binding! id prefixed-id bare-id)
    (-> identifier? identifier? identifier? void?)
    (free-id-table-set! type-label-bindings id (type-binding prefixed-id bare-id)))
  (define/contract (type-binding-value id)
    (-> identifier? (or/c type-binding? #f))
    (free-id-table-ref type-label-bindings id #f)))

(begin-for-syntax
  (define-syntax-class type-binding-id
    #:description "type binding"
    #:attributes [prefixed-id bare-id]
    [pattern x:id
             #:do [(define type-binding (type-binding-value #'x))]
             #:when type-binding
             #:attr prefixed-id (type-binding-prefixed-id type-binding)
             #:attr bare-id (type-binding-bare-id type-binding)])

  (define-splicing-syntax-class kind-kw
    #:description "#:kind keyword"
    (pattern (~optional (~seq #:kind kind)
                        #:defaults ([kind #'#f]))))
 
  (define-splicing-syntax-class link-target?-kw
    #:description "#:link-target? keyword"
    (pattern (~seq #:link-target? expr))
    (pattern (~seq)
             #:with expr #'#t)))

(define-syntax-parser deftycon
  [(_ k:patched/kind-kw lt:patched/link-target?-kw l:patched/literals-kw
      {~and spec (type:type-binding-id . spec-body)}
      subs:patched/subs-kw c:patched/contracts-kw desc ...)
   (quasisyntax/loc this-syntax
     (patched/defform
      {~? {~@ . k} {~@ #:kind "type constructor"}} {~? {~@ . lt}} {~? {~@ . l}}
      #:id type.prefixed-id
      #,(datum->syntax #'here
                       (cons (datum->syntax #'type.bare-id
                                            (syntax-e #'type.bare-id)
                                            #'type
                                            #'type.bare-id)
                             #'spec-body)
                       #'spec)
      {~? {~@ . subs}} {~? {~@ . c}} desc ...))])

(define-syntax-parser deftycon*
  [(_ k:patched/kind-kw lt:patched/link-target?-kw l:patched/literals-kw
      [{~and spec (type:type-binding-id . spec-body)} ...+]
      subs:patched/subs-kw c:patched/contracts-kw desc ...)
   #:with defined-id (first (attribute type.prefixed-id))
   #:with [spec* ...] (for/list ([spec (in-list (attribute spec))]
                                 [type (in-list (attribute type))]
                                 [display-id (in-list (attribute type.bare-id))]
                                 [spec-body (in-list (attribute spec-body))])
                        (datum->syntax #f
                                       (cons (datum->syntax display-id
                                                            (syntax-e display-id)
                                                            type
                                                            display-id)
                                             spec-body)
                                       spec
                                       spec))
   (quasisyntax/loc this-syntax
     (patched/defform*
      {~? {~@ . k} {~@ #:kind "type constructor"}} {~? {~@ . lt}}
      #:id defined-id
      {~? {~@ . l}}
      [spec* ...]
      {~? {~@ . subs}} {~? {~@ . c}}
      desc ...))])

(define-syntax-parser deftype
  [(_ k:patched/kind-kw lt:patched/link-target?-kw d:patched/id-kw type:type-binding-id
      desc ...)
   (quasisyntax/loc this-syntax
     (patched/defidform
      {~? {~@ . k} {~@ #:kind "type"}} {~? {~@ . lt}}
      #:id type.prefixed-id
      #,(datum->syntax #'type.bare-id (syntax-e #'type.bare-id) #'type #'type.bare-id)
      desc ...))])

(define-syntax-parser defdata
  [(_ kind:kind-kw 
      lt:link-target?-kw
      type:type-constructor-spec
      constructor:data-constructor-spec ...
      desc ...)
   #:with tag:type-binding-id #'type.tag
   #'(let-syntax ([type.arg (make-variable-id 'type.arg)] ...)
       (*defdata kind.kind
                 lt.expr
                 (quote-syntax tag.prefixed-id)
                 (quote-syntax tag.bare-id)
                 (list (racket type.arg) ...)
                 (list (quote-syntax constructor.tag) ...)
                 (list (list (racket constructor.arg) ...) ...)
                 (lambda () (list desc ...))))])

(define-syntax-parser defclass
  #:datum-literals [->]
  [(_ kind:kind-kw 
      lt:link-target?-kw
      {~optional {~seq #:super [super-constraint ...]}
                 #:defaults ([[super-constraint 1] '()])}
      (name:type-binding-id var-id:id ...)
      {~optional {~seq #:fundeps [[fundep-determinant:id ...+ -> fundep-dependent:id ...+] ...]}
                 #:defaults ([[fundep-determinant 2] '()] [[fundep-dependent 2] '()])}
      [method-id:id method-type:expr] ...
      desc ...)
   #'(let-syntax ([var-id (make-variable-id 'var-id)] ...)
       (*defclass kind.kind
                  lt.expr
                  (quote-syntax name.prefixed-id)
                  (quote-syntax name.bare-id)
                  (list (racket super-constraint) ...)
                  (list (racket var-id) ...)
                  (list (cons (list (racket fundep-determinant) ...)
                              (list (racket fundep-dependent) ...))
                        ...)
                  (list (racket method-id) ...)
                  (list (racket method-type) ...)
                  (lambda () (list desc ...))))])

(define-syntax-parser defmethod
  [(_ body ...)
   #'(nested #:style 'inset (defthing body ...))])

;; copied from scribble/private/manual-vars.rkt
(define boxed-style 
  (make-style 'boxed (list (make-attributes (list (cons 'class "RBoxed"))))))

(define (*defdata kind link? type-orig-id type-bare-id type-args ctor-ids ctor-argss content-thunk)
  (define (make-constructor binding-id display-id args)
    (let* ([content (to-element display-id #:defn? #t)]
           [ref-content (to-element display-id)]
           [thing-id ((id-to-target-maker binding-id #t)
                      content
                      (λ (tag)
                        (make-toc-target2-element
                         #f
                         (make-index-element
                          #f
                          content
                          tag
                          (list (symbol->string (syntax-e display-id)))
                          (list ref-content)
                          (with-exporting-libraries
                           (λ (libs) (make-thing-index-desc (syntax-e display-id) libs))))
                         tag
                         ref-content)))])
      (if (empty? args)
          thing-id
          (list (racketparenfont "(")
                thing-id
                (hspace 1)
                (add-between args (hspace 1))
                (racketparenfont ")")))))
  (make-splice
   (cons
    (make-blockquote
     (make-style 'vertical-inset null)
     (list
      (make-table
       boxed-style
       (list (list ((add-background-label (or kind "datatype"))
                    (top-align "argcontract"
                               (list
                                (list
                                 (list (make-omitable-paragraph
                                        (list (racketparenfont "(")
                                              (racket data)
                                              (hspace 1)
                                              (make-constructor type-orig-id type-bare-id type-args)
                                              (for/list ([ctor-id (in-list ctor-ids)]
                                                         [ctor-args (in-list ctor-argss)])
                                                (list (linebreak)
                                                      (hspace 2)
                                                      (make-constructor ctor-id ctor-id ctor-args)))
                                              (racketparenfont ")")))))))))))))
    (content-thunk))))

(define (*defclass kind link? class-orig-id class-bare-id super-constraints var-ids fundeps method-ids
                   method-types content-thunk)
  (define class-head
    (let* ([content (to-element class-bare-id #:defn? #t)]
           [ref-content (to-element class-bare-id)]
           [thing-id ((id-to-target-maker class-orig-id #t)
                      content
                      (λ (tag)
                        (make-toc-target2-element
                         #f
                         (make-index-element
                          #f
                          content
                          tag
                          (list (symbol->string (syntax-e class-bare-id)))
                          (list ref-content)
                          (with-exporting-libraries
                           (λ (libs) (make-thing-index-desc (syntax-e class-bare-id) libs))))
                         tag
                         ref-content)))])
      (list (racketparenfont "(") thing-id (if (empty? var-ids) '() (hspace 1))
            (add-between var-ids (hspace 1)) (racketparenfont ")"))))
  (make-splice
   (cons
    (make-blockquote
     (make-style 'vertical-inset null)
     (list
      (make-table
       boxed-style
       (append
        (list (list ((add-background-label (or kind "typeclass"))
                     (list (make-omitable-paragraph
                            (list (racketparenfont "(") (racket class) (hspace 1)
                                  (if (empty? super-constraints) '()
                                      (list (add-between super-constraints (hspace 1))
                                            (hspace 1) (racket =>) (hspace 1)))
                                  class-head
                                  (if (and (empty? fundeps) (empty? method-ids))
                                      (racketparenfont ")")
                                      '())))))))
        (if (empty? fundeps) '()
            (list
             (list
              (list
               (make-table
                "RktBlk"
                (list (list (list (make-omitable-paragraph
                                   (list (hspace 2) (racket #:fundeps)
                                         (hspace 1) (racketparenfont "["))))
                            (list (make-table #f (for/list ([fundep (in-list fundeps)]
                                                            [i (in-naturals)])
                                                   (list
                                                    (list
                                                     (make-omitable-paragraph
                                                      (list (racketparenfont "[")
                                                            (add-between (car fundep) (hspace 1))
                                                            (hspace 1) (racket ->) (hspace 1)
                                                            (add-between (cdr fundep) (hspace 1))
                                                            (racketparenfont "]")
                                                            (if (= i (sub1 (length fundeps)))
                                                                (list (racketparenfont "]")
                                                                      (if (empty? method-ids)
                                                                          (racketparenfont ")")
                                                                          '()))
                                                                '())))))))))))))))
        (for/list ([method-id (in-list method-ids)]
                   [method-type (in-list method-types)]
                   [i (in-naturals)])
          (list (list (make-omitable-paragraph
                       (list (hspace 2) (racketparenfont "[")
                             method-id (hspace 1) (racket :) (hspace 1) method-type
                             (racketparenfont "]")
                             (if (= i (sub1 (length method-ids)))
                                 (racketparenfont ")")
                                 '()))))))))))
    (content-thunk))))

(define (to-flow e) (nested-flow (make-style #f '()) (list (make-omitable-paragraph (list e)))))

(define top-align-styles (make-hash))
(define (top-align style-name cols)
  (list
   (if (null? cols)
       (make-table style-name '())
       (let* ([n (length (car cols))]
              [k (cons style-name n)])
         (make-table
          (hash-ref top-align-styles
                    k
                    (lambda ()
                      (define s
                        (make-style style-name
                                    (list (make-table-columns (for/list ([i n])
                                                                (make-style #f '(top)))))))
                      (hash-set! top-align-styles k s)
                      s))
          cols)))))
