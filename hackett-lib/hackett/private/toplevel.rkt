#lang racket/base

; This module implements #%top-interaction for the Hackett REPL. It does some tricks to make Hackett
; forms cooperate more nicely with the top level while still being able to do things like print the
; types of expressions evaluated at the REPL.
;
; The fundamental problem is that Hackett relies heavily on compile-time bindings and local-expand,
; but compile-time bindings are complicated at the top level. For example, imagine a macro being
; expanded with local-expand produces the following form:
;
;   (begin
;     (define-syntax x <expr>)
;     (some-macro x))
;
; If some-macro calls local-expand on the x provided as a subform, the result will be an unbound
; identifier error, since the (define-syntax ....) form has not yet been evaluated.
;
; This is only a problem, however, if the code in question is being expanded with local-expand. At the
; top level, when the expander sees a (begin ....) form, it will intelligently evaluate the forms in
; order *before* proceeding to expand subsequent forms. This is a problem, however, because we *need*
; to expand subsequent forms in order to check what the final expression’s type is to print type
; information.
;
; To fix this, we can implement a sort of “trampoline” in #%top-interaction that will perform partial
; expansion until we are sure we are dealing with an expression. For example, imagine the user submits
; the following form at the REPL:
;
;   > (m1 x)
;
; This will be wrapped by the expander in our #%top-interaction, so the entire form will be this:
;
;   (#%top-interaction m1 x)
;
; Now, in this case, m1 may be a macro. To find out, we can perform partial expansion using
; local-expand with (kernel-form-identifier-list) as the stop list. This may produce an expression, in
; which case we’re finished, and we can print the expression’s type if it has one. If we have a
; definition, we’re also finished, and we can expand to the definition without doing anything else. If
; we have a begin, on the other hand, we need to be more clever. Imagine (m1 x) expands into the
; following:
;
;   (begin
;     (define-syntax x0 <expr>)
;     (m2 x x0))
;
; Crucially, we *cannot* call local-expand on (m2 x x0), because if we do, it will be expanded in a
; context without the x0 compile-time binding available! Instead, we need to yield to the expander,
; which we can do by expanding to the following:
;
;   (begin
;     (define-syntax x0 <expr>)
;     (#%top-interaction m2 x x0))
;
; The expander will evaluate the top level definition, then yield control back to our
; #%top-interaction, and we can continue the partial expansion process.
;
; Much of this process is similar to the process performed by the functions in syntax/toplevel, but
; that module uses expand-syntax-to-top-form instead of local-expand, and it evaluates forms with
; eval-syntax in the current namespace instead of yielding control to the expander. That avoids the
; need to trampoline, but it isn’t possible to use during the extent of #%top-interaction’s expansion,
; since we are at phase 1, but the forms need to be evaluated at phase 0.
;
; The story is complicated slightly further by the additional need to perform Hackett’s dictionary
; elaboration passes, even on parts of the form that aren’t relevant for printing type information.
; Since elaboration involves complete expansion, the aforementioned trampolining must be formed prior
; to elaboration. Once we discover a non-begin form, we wrap it in a form that will perform
; elaboration.

(require (for-syntax racket/base
                     racket/match
                     syntax/kerncase
                     threading

                     hackett/private/expand+elaborate
                     hackett/private/typecheck
                     hackett/private/util/stx)
         racket/promise
         syntax/parse/define

         (submod hackett/private/expand+elaborate elaborate-top-transformer)
         hackett/private/type-reqprov
         (only-in hackett/private/base τ⇒! τ⇐!)
         (only-in (unmangle-types-in #:no-introduce hackett/private/kernel) String)
         (only-in hackett/private/kernel [#%app @%app])
         (only-in hackett/private/prim/base show))

(provide @%top-interaction)

(struct repl-result [value type]
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc result port mode)
     (fprintf port ": ~a\n~a" (repl-result-type result) (repl-result-value result)))])
(struct type-result [type]
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc result port mode)
     (fprintf port ": ~a" (type-result-type result)))])

(define-syntax-parser @%top-interaction
  [(_ . form)
   (syntax-parse (value-namespace-introduce #'form)
     [(#:type ~! expr:expr)
      #'(infer+print-type expr)]
     [form*
      #'(infer+elaborate+print-value+type form*)])])

(define-syntax-parser infer+print-type
  [(_ expr:expr)
   (match-let-values ([(_ τ_e) (τ⇒! #'expr)])
     #`(type-result '#,(type->string (apply-current-subst τ_e))))])

(define-syntax infer+elaborate+print-value+type
  (let ([stops (cons #'#%elaborate-top (kernel-form-identifier-list))])
    (syntax-parser
      [(_ form)
       (syntax-parse (local-expand #'form 'top-level stops)
         #:context this-syntax
         #:literal-sets [kernel-literals]
         #:literals [#%elaborate-top]
         [{~or (begin)
               ({~or #%require begin-for-syntax define-syntaxes define-values} . _)}
          #`(elaborate #,this-syntax)]
         [(begin form ... form*)
          (syntax/loc this-syntax
            (begin (elaborate form) ... (infer+elaborate+print-value+type form*)))]
         [(#%elaborate-top form)
          #'(elaborate form)]
         [expr
          #'(elaborate (infer+print-value+type expr))])])))

(define-syntax-parser elaborate
  [(_ form)
   (local-expand+elaborate #'form)])

(define-syntax-parser infer+print-value+type
  [(_ expr:expr)
   (match-let*-values ([(e- τ_e) (τ⇒! #'expr)]
                       [(e-/show) (τ⇐! (quasisyntax/loc this-syntax
                                         (@%app show #,e-))
                                       (expand-type #'String))])
     #`(repl-result (force #,e-/show) (type-string #,τ_e)))])

(define-syntax type-string
  (make-elaborating-transformer
   (syntax-parser
     [(_ t)
      (match (syntax-local-elaborate-pass)
        [(or 'expand 'elaborate)
         (syntax-local-elaborate-defer this-syntax)]
        ['finalize
         #`'#,(type->string (apply-current-subst #'t))])])))
