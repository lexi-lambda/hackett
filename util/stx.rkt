#lang racket/base

(require racket/contract
         racket/list
         racket/match
         syntax/id-table
         syntax/parse)

(provide
 (contract-out
  [make-variable-like-transformer/thunk ((-> syntax?) . -> . (syntax? . -> . syntax?))]
  [collect-properties (syntax? any/c . -> . list?)]
  [free-id-table-union (immutable-free-id-table? immutable-free-id-table?
                        . -> . immutable-free-id-table?)]))

;; ---------------------------------------------------------------------------------------------------
;; general syntax object utilities

; Like make-variable-like-transformer, except that the argument is a thunk that produces syntax
; instead of a syntax object directly.
(define (make-variable-like-transformer/thunk ref-stx)
  (lambda (stx)
    (syntax-case stx ()
      [id
       (identifier? #'id)
       (ref-stx)]
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
