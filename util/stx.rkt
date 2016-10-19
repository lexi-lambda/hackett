#lang curly-fn racket/base

(require racket/contract
         racket/format
         racket/list
         racket/match
         racket/string
         syntax/id-table
         syntax/parse)

(provide
 (contract-out
  [make-variable-like-transformer/thunk ((or/c (-> syntax?)
                                               (syntax? . -> . syntax?))
                                         . -> . (syntax? . -> . syntax?))]
  [collect-properties (syntax? any/c . -> . list?)]
  [identifiers->english-list ((listof identifier?) . -> . string?)]
  [original-for-check-syntax (syntax? . -> . syntax?)]
  [original-for-check-syntax? (syntax? . -> . boolean?)]
  [propagate-original-for-check-syntax (syntax? syntax? . -> . syntax?)]
  [free-id-table-union (immutable-free-id-table? immutable-free-id-table?
                        . -> . immutable-free-id-table?)]
  [property-proxy (any/c . -> . syntax?)]
  [property-proxy-value (syntax? . -> . any/c)]))

;; ---------------------------------------------------------------------------------------------------
;; general syntax object utilities

; Like make-variable-like-transformer, except that the argument is a thunk that produces syntax
; instead of a syntax object directly.
(define (make-variable-like-transformer/thunk ref-stx)
  (lambda (stx)
    (syntax-case stx ()
      [id
       (identifier? #'id)
       (if (procedure-arity-includes? ref-stx 1)
           (ref-stx #'id)
           (ref-stx))]
      [(id . args)
       (let ([stx* (list* '#%app #'id (cdr (syntax-e stx)))])
         (datum->syntax stx stx* stx stx))])))

; Flattens a tree into a list. Designed for use with syntax properties due to the way the syntax
; property merging algorithm works.
(define/match (flatten-syntax-property-value val)
  [(#f)
   '()]
  [((cons a b))
   (append (flatten-syntax-property-value a)
           (flatten-syntax-property-value b))]
  [((? list?))
   (append-map flatten-syntax-property-value val)]
  [(_)
   (list val)])

; Given a syntax object, recursively collects all properties with the given key, then flattens
; them using flatten-syntax-property-value to ensure all properties are included, even ones merged
; by the macroexpander.
(define (collect-properties stx key)
  (define (get-properties stx)
    (flatten-syntax-property-value (syntax-property stx key)))
  (let recur ([stx stx])
    (syntax-parse stx
      [(elem ...+ . cdr)
       (append (get-properties this-syntax)
               (append-map recur (attribute elem))
               (recur #'cdr))]
      [_ (get-properties this-syntax)])))

; Renders a list of quoted identifiers to an English string, including an Oxford comma. Useful for
; error messages.
(define identifiers->english-list
  (match-lambda
    [(list id)  (~a "‘" (symbol->string (syntax-e id)) "’")]
    [(list a b) (~a "‘" (symbol->string (syntax-e a)) "’ and ‘" (symbol->string (syntax-e b)) "’")]
    [ids        (string-join (map #{symbol->string (syntax-e %)} ids) "’, ‘"
                             #:before-last "’, and ‘" #:before-first "‘" #:after-last "’")]))

; Marks an identifier as original with the property that Check Syntax understands.
(define (original-for-check-syntax stx)
  (syntax-property stx 'original-for-check-syntax #t))

; Checks if an identifier is considered original by Check Syntax. Note that if the identifier has been
; provided to a syntax transformer, it has a macro-introduction scope on it, so you must call
; syntax-local-introduce first to get a completely accurate answer.
(define (original-for-check-syntax? stx)
  (or (syntax-original? stx)
      (syntax-property stx 'original-for-check-syntax)))

; Marks an identifier as original for check syntax if the provided piece of syntax is considered
; original by check syntax. The same caveat about macro-introduction scopes applies to the src-stx
; argument of this function as mentioned for original-for-check-syntax?.
(define (propagate-original-for-check-syntax src-stx result-stx)
  (if (original-for-check-syntax? src-stx)
      (original-for-check-syntax result-stx)
      result-stx))

;; ---------------------------------------------------------------------------------------------------
;; free id tables

; Performs a left-biased union of immutable free-id tables.
(define (free-id-table-union a b)
  (let ([t (make-free-id-table)])
    (for ([(k v) (in-free-id-table b)])
      (free-id-table-set! t k v))
    (for ([(k v) (in-free-id-table a)])
      (free-id-table-set! t k v))
    (make-immutable-free-id-table t)))

;; ---------------------------------------------------------------------------------------------------
;; property proxies

; Sometimes, it is useful to embed a value in a piece of syntax. Normally, this is easily achievable
; using quasisyntax/unsyntax, but in the case of embedding prefab structs, the macroexpander will
; mess with their contents. Specifically, if a prefab struct contains a syntax object, then the prefab
; struct is embedded in a piece of syntax, the macroexpander will “flatten” it such that the syntax
; information is lost.
;
; An easy way around this is to attach the value to a syntax property, which the macroexpander will
; not touch. These are some very simple helper functions for making that intent explicit.

(define (property-proxy val)
  (syntax-property #'proxy 'proxy-value val))

(define (property-proxy-value stx)
  (syntax-property stx 'proxy-value))
