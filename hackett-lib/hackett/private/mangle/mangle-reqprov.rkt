#lang racket/base

(provide make-unmangling-require-transformer
         make-mangling-provide-transformer)

(require racket/function
         racket/list
         racket/provide-transform
         racket/require-transform
         syntax/parse
         (only-in syntax/parse [attribute @])
         threading
         (for-template racket/base)
         "mangle-identifier.rkt"
         "mangle-import-export.rkt")

;; ---------------------------------------------------------

;; #:mangle-prefix String
;; #:introducer StxIntroducer
;; ->
;; RequireTransformer
(define (make-unmangling-require-transformer id-unmangler)
  (make-require-transformer
   (syntax-parser
     [(_ {~alt {~optional {~or {~and #:no-introduce no-introduce?}
                               {~seq #:prefix prefix:id}}}
               {~optional {~and #:only only?}}}
         ...
         require-spec ...)
      #:do [(define id-unmangler*
              (let* ([unm id-unmangler]
                     [unm (if (or (@ no-introduce?) (@ prefix))
                            (no-introduce/unmangler unm)
                            unm)]
                     [unm (if (@ prefix)
                            (prefix/unmangler (syntax-e (@ prefix)) unm)
                            unm)])
                unm))

            (define-values [imports sources]
              (expand-import #'(combine-in require-spec ...)))]

      (values (for*/list ([i (in-list imports)]
                          [i* (in-value (unmangle-import i id-unmangler*))]
                          #:when (if (@ only?) i* #t))
                (or i* i))
              sources)])))

;; #:mangle-prefix String
;; #:introducer StxIntroducer
;; ->
;; ProvideTransformer
(define (make-mangling-provide-transformer id-mangler)
  (make-provide-transformer
   (λ (stx modes)
     (syntax-parse stx
       [(_ {~optional {~and #:no-introduce no-introduce?}} provide-spec ...)
        #:do [(define id-mangler*
                (if (@ no-introduce?)
                    (no-introduce/mangler id-mangler)
                    id-mangler))

              (define exports
                (expand-export (syntax/loc this-syntax
                                 (combine-out provide-spec ...))
                               modes))]

        (for/list ([e (in-list exports)])
          (mangle-export e id-mangler*))]))))
