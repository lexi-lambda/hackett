#lang racket/base

(provide make-string-mangler)

(require threading
         racket/list)
(module+ test
  (require rackunit))

;; A StringMangler is a function:
;;   String -> String

;; A StringUnmangler is a function:
;;   String -> [Maybe String]

;; #:prefix String -> (values StringMangler StringUnmangler)
(define (make-string-mangler #:prefix mangle-prefix)
  (define mangled-regexp
    (regexp (string-append "^"
                           (regexp-quote mangle-prefix)
                           "(.*)$")))

  ;; String -> String
  (define (mangle-string name)
    (string-append mangle-prefix name))

  ;; String -> [Maybe String]
  (define (unmangle-string name)
    (and~> (regexp-match mangled-regexp name) second))

  (values mangle-string unmangle-string))

;; ---------------------------------------------------------

(module+ test
  (define pre "#%hackett-test:")
  (define-values [mangle unmangle]
    (make-string-mangler #:prefix pre))

  (check-equal? (unmangle (mangle "ahotenus")) "ahotenus")
  (check-equal? (unmangle (mangle "jatkae")) "jatkae")
  (check-equal? (unmangle "ahotenus") #false)
  )

