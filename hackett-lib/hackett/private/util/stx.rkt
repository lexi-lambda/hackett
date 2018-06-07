#lang racket/base

(require (for-syntax racket/base)
         (for-template racket/base
                       syntax/parse)
         racket/contract
         racket/list
         racket/match
         syntax/parse
         syntax/parse/define
         syntax/parse/experimental/template
         threading)

(provide (contract-out [replace-stx-loc (-> syntax? syntax? syntax?)]
                       [make-variable-like-transformer (-> (or/c syntax? (-> identifier? syntax?))
                                                           (-> syntax? syntax?))]
                       [make-pattern-like-pattern-expander (-> (or/c syntax? (-> identifier? syntax?))
                                                                pattern-expander?)]
                       [make-trampolining-expression-transformer (-> (-> syntax? syntax?)
                                                                     (-> syntax? syntax?))]
                       [preservable-property->expression (-> any/c syntax?)]
                       [generate-bound-temporaries (-> (or/c syntax? list?) (listof identifier?))]
                       [generate-bound-temporary (-> any/c identifier?)]
                       [adjust-property (-> syntax? any/c (-> any/c any/c) syntax?)]
                       [recursively-adjust-property (-> syntax? any/c (-> any/c any/c) syntax?)])
         syntax/loc/props quasisyntax/loc/props template/loc/props quasitemplate/loc/props)

; These two functions are taken with modifications from macrotypes/stx-utils, which implement a
; version of make-variable-like-transformer from syntax/transformer that cooperates better with
; typechecking.
(define (replace-stx-loc stx srcloc)
  (let ([stx* (syntax-disarm stx #f)])
    (syntax-rearm (datum->syntax stx* (syntax-e stx*) srcloc stx) stx)))

(define (make-variable-like-transformer ref-stx)
  (syntax-parser
    [_:id
     (replace-stx-loc (if (procedure? ref-stx) (ref-stx this-syntax) ref-stx) this-syntax)]
    [(head:id . args)
     (datum->syntax this-syntax (list* '#%app #'head #'args) this-syntax this-syntax)]))

(define (make-pattern-like-pattern-expander ref-stx)
  (pattern-expander
   (syntax-parser
     [_:id
      (replace-stx-loc (if (procedure? ref-stx) (ref-stx this-syntax) ref-stx) this-syntax)]
     [(head:id . args)
      (syntax/loc this-syntax ({~and head} . args))])))

(define ((make-trampolining-expression-transformer proc) stx)
  (if (eq? (syntax-local-context) 'expression)
      (proc stx)
      (datum->syntax stx (list (replace-stx-loc #'#%expression stx) stx) stx)))

; Sometimes, it is useful to embed a value in a piece of syntax. Normally, this is easily achievable
; using quasisyntax/unsyntax, but in the case of embedding prefab structs, the macroexpander will
; mess with their contents. Specifically, if a prefab struct contains a syntax object, then the prefab
; struct is embedded in a piece of syntax, the macroexpander will “flatten” it such that the syntax
; information is lost.
;
; A hacky way around this is to convert values to expressions that evaluate to themselves, then embed
; those into the resulting syntax instead of the values directly.
(define preservable-property->expression
  (match-lambda
    [(and (app prefab-struct-key (? values prefab-key))
          (app struct->vector (vector _ fields ...)))
     #`(make-prefab-struct '#,prefab-key #,@(map preservable-property->expression fields))]
    [(? list? lst)
     #`(list #,@(map preservable-property->expression lst))]
    [(cons a b)
     #`(cons #,(preservable-property->expression a)
             #,(preservable-property->expression b))]
    [(? syntax? stx)
     #`(quote-syntax #,stx)]
    [(and (or (? boolean?) (? symbol?) (? number?) (? char?) (? string?) (? bytes?) (? regexp?))
          datum)
     #`(quote #,datum)]
    [other
     (error 'preservable-property->expression
            "disallowed value within preserved syntax property\n  value: ~e"
            other)]))

; Like syntax/loc and friends, but copy properties from the source syntax object in addition to source
; location.
(define-syntaxes [syntax/loc/props quasisyntax/loc/props template/loc/props quasitemplate/loc/props]
  (let ()
    (define (make-syntax/loc/props name syntax-id)
      (syntax-parser
        [(_ from-stx-expr:expr {~describe "template" template})
         #`(let ([from-stx from-stx-expr])
             (unless (syntax? from-stx)
               (raise-argument-error '#,name "syntax?" from-stx))
             (let* ([stx (#,syntax-id template)]
                    [stx* (syntax-disarm stx #f)])
               (syntax-rearm (datum->syntax stx* (syntax-e stx*) from-stx from-stx) stx)))]))
    (values (make-syntax/loc/props 'syntax/loc/props #'syntax)
            (make-syntax/loc/props 'quasisyntax/loc/props #'quasisyntax)
            (make-syntax/loc/props 'template/loc/props #'template)
            (make-syntax/loc/props 'quasitemplate/loc/props #'quasitemplate))))

; Like generate-temporaries, but also binds each identifier to a runtime binding. Though the
; identifier will always be out of context if actually used in an expanded program, when used with
; local-expand, it will be left untouched. Later, it’s possible to arrange for the identifier to be
; placed in binding position of some other form.
(define (generate-bound-temporaries stx-pair)
  (let* ([intdef-ctx (syntax-local-make-definition-context)]
         [ids (generate-temporaries stx-pair)])
    (syntax-local-bind-syntaxes ids #f intdef-ctx)
    (map (λ (id) (internal-definition-context-introduce intdef-ctx id)) ids)))

; Like generate-temporary but with the binding behavior of generate-bound-temporaries.
(define (generate-bound-temporary [name-base 'g])
  (first (generate-bound-temporaries (list name-base))))

; Modifies the property of a syntax object by applying a procedure to its value. If the syntax object
; does not contain any such property, the original syntax object is returned. Otherwise, the
; property’s value is recursively traversed as a tree of cons pairs, and the procedure is applied to
; each leaf to produce a new result.
(define (adjust-property stx key proc)
  (let ([val (syntax-property stx key)])
    (if val
        (syntax-property stx key
                         (let loop ([val val])
                           (cond [(list? val) (map loop val)]
                                 [(pair? val) (cons (loop (car val)) (loop (cdr val)))]
                                 [else (proc val)])))
        stx)))

; Like adjust-property, but recursively walks the syntax object and applies the function to each
; subform. Handles arming and disarming as necessary.
(define (recursively-adjust-property stx key proc)
  (let loop ([stx stx])
    (let* ([disarmed (syntax-disarm stx #f)]
           [result (~> (match (syntax-e disarmed)
                         [(list a ...) (map loop a)]
                         [(list* a ..1 b) (append (map loop a) (loop b))]
                         [a a])
                       (datum->syntax disarmed _ disarmed disarmed)
                       (adjust-property key proc)
                       (syntax-rearm stx))])
      (when (syntax-tainted? result)
        (raise-syntax-error 'recursively-adjust-property "could not disarm syntax object" stx))
      result)))
