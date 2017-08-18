#lang racket/base

(require (for-label hackett)

         (for-syntax racket/base)

         racket/list
         scribble/struct
         scribble/scheme
         scribble/manual-struct
         scribble/manual
         scribble/decode
         scribble/html-properties
         syntax/parse/define

         (only-in scribble/core make-style make-table-columns nested-flow)
         (only-in scribble/private/manual-vars add-background-label)
         (only-in scribble/private/manual-bind
                  id-to-target-maker with-exporting-libraries
                  definition-site)

         (only-meta-in 1 hackett/private/adt))

(provide defdata defclass defmethod)

(begin-for-syntax
  (define-splicing-syntax-class kind-kw
    #:description "#:kind keyword"
    (pattern (~optional (~seq #:kind kind)
                        #:defaults ([kind #'#f]))))
 
  (define-splicing-syntax-class link-target?-kw
    #:description "#:link-target? keyword"
    (pattern (~seq #:link-target? expr))
    (pattern (~seq)
             #:with expr #'#t))

  (define-syntax-class id-or-false
    (pattern i:id)
    (pattern #f #:with i #'#f))
   
  (define-splicing-syntax-class id-kw
    #:description "#:id keyword"
    (pattern (~optional (~seq #:id [key:id-or-false expr])
                        #:defaults ([key #'#f]
                                    [expr #'#f])))))

(define-syntax-parser defdata
  [(_ kind:kind-kw 
      lt:link-target?-kw
      type:type-constructor-spec
      constructor:data-constructor-spec ...
      desc ...)
   #'(let-syntax ([type.arg (make-variable-id 'type.arg)] ...)
       (*defdata kind.kind
                 lt.expr
                 (quote-syntax type.tag)
                 'type.tag
                 (list (racket type.arg) ...)
                 (list (quote-syntax constructor.tag) ...)
                 (list 'constructor.tag ...)
                 (list (list (racket constructor.arg) ...) ...)
                 (lambda () (list desc ...))))])

(define-syntax-parser defclass
  [(_ kind:kind-kw 
      lt:link-target?-kw
      {~optional {~seq #:super [super-constraint ...]}
                 #:defaults ([[super-constraint 1] '()])}
      (name:id var-id:id)
      [method-id:id method-type:expr] ...
      desc ...)
   #'(let-syntax ([var-id (make-variable-id 'var-id)])
       (*defclass kind.kind
                  lt.expr
                  (quote-syntax name)
                  'name
                  (list (racket super-constraint) ...)
                  (racket var-id)
                  (list (racket method-id) ...)
                  (list (racket method-type) ...)
                  (lambda () (list desc ...))))])

(define-syntax-parser defmethod
  [(_ body ...)
   #'(nested #:style 'inset (defthing body ...))])

;; copied from scribble/private/manual-vars.rkt
(define boxed-style 
  (make-style 'boxed (list (make-attributes (list (cons 'class "RBoxed"))))))

(define (*defdata kind link? type-id type-name type-args ctor-ids ctor-names ctor-argss content-thunk)
  (define (make-constructor stx-id name args)
    (let* ([content (to-element (make-just-context name stx-id) #:defn? #t)]
           [ref-content (to-element (make-just-context name stx-id))]
           [thing-id ((id-to-target-maker stx-id #t)
                      content
                      (λ (tag)
                        (make-toc-target2-element
                         #f
                         (make-index-element
                          #f
                          content
                          tag
                          (list (symbol->string name))
                          (list ref-content)
                          (with-exporting-libraries
                           (λ (libs) (make-thing-index-desc name libs))))
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
                                              (make-constructor type-id type-name type-args)
                                              (for/list ([ctor-id (in-list ctor-ids)]
                                                         [ctor-name (in-list ctor-names)]
                                                         [ctor-args (in-list ctor-argss)])
                                                (list (linebreak)
                                                      (hspace 2)
                                                      (make-constructor ctor-id ctor-name ctor-args)))
                                              (racketparenfont ")")))))))))))))
    (content-thunk))))

(define (*defclass kind link? class-id class-name super-constraints var-id method-ids method-types
                   content-thunk)
  (define class-head
    (let* ([content (to-element (make-just-context class-name class-id) #:defn? #t)]
           [ref-content (to-element (make-just-context class-name class-id))]
           [thing-id ((id-to-target-maker class-id #t)
                      content
                      (λ (tag)
                        (make-toc-target2-element
                         #f
                         (make-index-element
                          #f
                          content
                          tag
                          (list (symbol->string class-name))
                          (list ref-content)
                          (with-exporting-libraries
                           (λ (libs) (make-thing-index-desc class-name libs))))
                         tag
                         ref-content)))])
      (list (racketparenfont "(") thing-id (hspace 1) var-id (racketparenfont ")"))))
  (make-splice
   (cons
    (make-blockquote
     (make-style 'vertical-inset null)
     (list
      (make-table
       boxed-style
       (list (list ((add-background-label (or kind "typeclass"))
                    (top-align "argcontract"
                               (list
                                (list
                                 (list (make-omitable-paragraph
                                        (list (racketparenfont "(")
                                              (racket class) (hspace 1)
                                              (if (empty? super-constraints) '()
                                                  (list (add-between super-constraints (hspace 1))
                                                        (hspace 1) (racket =>) (hspace 1)))
                                              class-head
                                              (for/list ([method-id (in-list method-ids)]
                                                         [method-type (in-list method-types)])
                                                (list (linebreak)
                                                      (hspace 2)
                                                      (racketparenfont "[")
                                                      method-id
                                                      (hspace 1)
                                                      (racket :)
                                                      (hspace 1)
                                                      method-type
                                                      (racketparenfont "]")))
                                              (racketparenfont ")")))))))))))))
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
