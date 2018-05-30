#lang racket/base

(require racket/contract/base)
(provide (contract-out
          [prop:case-pattern-expander
           (struct-type-property/c (-> any/c (-> syntax? syntax?)))]
          [case-pattern-expander?
           (-> any/c boolean?)]
          [case-pattern-expander
           (-> (-> syntax? syntax?) case-pattern-expander?)]
          [case-pattern-expander-transformer
           (-> case-pattern-expander? (-> syntax? syntax?))]))

(require racket/local)

;; prop:case-pattern-expander is a struct-type-property
;; that contains one of:
;;  - [Self -> [Syntax -> Syntax]]

;; case-pattern-expander? : Any -> Boolean : CasePatternExpander

;; case-pattern-expander : [Syntax -> Syntax] -> CasePatternExpander

;; case-pattern-expander-transformer : CasePatternExpander -> [Syntax -> Syntax]

(define-values [prop:case-pattern-expander
                case-pattern-expander?
                case-pattern-expander-ref]
  (make-struct-type-property 'case-pattern-expander))

(define case-pattern-expander
  (local [(struct case-pattern-expander [transformer]
            #:property prop:case-pattern-expander
            (λ (self) (case-pattern-expander-transformer self)))]
    case-pattern-expander))

(define (case-pattern-expander-transformer cpe)
  (define get-transformer
    (case-pattern-expander-ref cpe))
  (get-transformer cpe))

