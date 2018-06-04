#lang racket/base

(provide make-id-mangler
         or/unmangler
         prefix/unmangler
         no-introduce/unmangler
         id-mangler
         no-introduce/mangler)

(require racket/match
         racket/syntax
         "mangle-string.rkt")

;; An IdMangler is an (id-mangler StxIntroducer StringMangler)
(struct id-mangler [introducer string-mangler])

;; An IdUnmangler is a function:
;;   Identifier -> [Maybe Identifier]

;; ---

;; A StringMangler is a function:
;;   String -> String

;; A StringUnmangler is a function:
;;   String -> [Maybe String]

;; A StxIntroducer is a function:
;;   Syntax -> Syntax
;; Which adds or removes scopes from the input without
;; changing the datum, source-location, or other properties.

;; ---

;; #:prefix String #:introducer StxIntroducer ->
;; (values IdMangler IdUnmangler)
(define (make-id-mangler #:prefix mangle-prefix #:introducer intro)
  (define-values [str-mangler str-unmangler]
    (make-string-mangler #:prefix mangle-prefix))
  (values (id-mangler intro str-mangler)
          (string-unmangler->id-unmangler str-unmangler intro)))

;; IdUnmangler ... -> IdUnmangler
(define ((or/unmangler . id-un*) x)
  (for/or ([id-un (in-list id-un*)])
    (id-un x)))

;; Symbol IdUnmangler -> IdUnmangler
(define ((prefix/unmangler pre id-un) x)
  (define unmangled (id-un x))
  (and unmangled
       (format-id unmangled "~a~a" pre unmangled
                  #:source unmangled #:props unmangled)))

;; IdUnmangler -> IdUnmangler
(define ((no-introduce/unmangler id-un) x)
  (define unmangled (id-un x))
  (and unmangled
       (datum->syntax x (syntax-e unmangled) x x)))

;; IdUnmangler -> IdUnmangler
(define (no-introduce/mangler id-mangler*)
  (match-define (id-mangler _ string-mangler) id-mangler*)
  (id-mangler values string-mangler))

;; ---------------------------------------------------------

;; StringUnmangler StxIntroducer -> IdUnmangler
(define ((string-unmangler->id-unmangler str-unmangle intro) x)
  (define name (symbol->string (syntax-e x)))
  (cond
    [(str-unmangle name)
     =>
     (λ (unmangled-name)
       (intro
        (datum->syntax x (string->symbol unmangled-name) x x)))]
    [else
     #false]))

;; ---------------------------------------------------------
