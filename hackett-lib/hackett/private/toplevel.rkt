#lang racket/base

(require racket/list
         racket/promise
         syntax/parse
         syntax/parse/define
         syntax/toplevel
         threading

         hackett/private/typecheck)

(provide @%top-interaction)

(define-simple-macro (@%top-interaction . form)
  (@%top-interaction*
   (expand-syntax-top-level-with-compile-time-evals/flatten
    (quote-syntax form))))

(define (@%top-interaction* forms)
  (if (empty? forms) (void)
      (begin0
        (for/last ([form (in-list forms)])
          (syntax-parse form
            #:literal-sets [kernel-literals]
            [({~or begin-for-syntax define-syntaxes} . _) (void)]
            [_ (force (eval-syntax form))]))
        (syntax-parse (last forms)
          #:literal-sets [kernel-literals]
          [({~or begin-for-syntax define-syntaxes define-values} . _)
           (void)]
          [e
           (and~>> (get-type #'e)
                   apply-current-subst
                   τ->string
                   (printf ": ~a\n"))]))))
