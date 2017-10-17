; The contents of this module include a copy of the implementation of ‘splicing-syntax-parameterize’
; from racket/splicing. Racket v6.11.0.1 or newer comes with this implementation, but this version is
; included for compatibility with older versions of Racket.
;
; The contents of this module are dual-licensed under the compatible ISC and MIT licenses, the former
; being the license of the entire Hackett project, the latter the license of the Racket distribution.
; The full text of the original license is reproduced below:
;
; Copyright 2017 PLT Design
;
; Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
; associated documentation files (the "Software"), to deal in the Software without restriction,
; including without limitation the rights to use, copy, modify, merge, publish, distribute,
; sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
; furnished to do so, subject to the following conditions:
;
; The above copyright notice and this permission notice shall be included in all copies or substantial
; portions of the Software.
;
; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
; NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES
; OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
; CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
#lang racket/base

(require (for-syntax racket/base) racket/splicing hackett/private/util/cond-expand)
(provide (all-from-out racket/splicing))

(cond-expand
 [(version<? (version) "6.11.0.2")
  (require (for-syntax syntax/kerncase
                       racket/syntax
                       racket/private/stxparamkey)
           (for-meta 2  ; for wrap-et-param
                     racket/base
                     syntax/kerncase)
           racket/private/stxparam)

  (provide splicing-syntax-parameterize)

  (module syntax/loc/props racket/base
    (require (for-syntax racket/base))
    (provide syntax/loc/props quasisyntax/loc/props)

    (define-syntaxes [syntax/loc/props quasisyntax/loc/props]
      (let ()
        (define (mk-syntax/loc/props syntax-id)
          (λ (stx)
            (syntax-case stx ()
              [(_ src-expr template)
               #`(let ([src src-expr])
                   (datum->syntax (quote-syntax #,stx) (syntax-e (#,syntax-id template)) src src))])))
        (values (mk-syntax/loc/props #'syntax)
                (mk-syntax/loc/props #'quasisyntax)))))

  (require (for-syntax 'syntax/loc/props)
           (for-meta 2 'syntax/loc/props))

  ;; ----------------------------------------

  (define-syntax (splicing-syntax-parameterize stx)
    (if (eq? 'expression (syntax-local-context))
        ;; Splicing is no help in an expression context:
        (do-syntax-parameterize stx #'let-syntaxes #f #f)
        ;; Let `syntax-parameterize' check syntax, then continue
        (do-syntax-parameterize stx #'ssp-let-syntaxes #t #t)))

  (define-syntax (ssp-let-syntaxes stx)
    (syntax-case stx ()
      [(_ ([(id) rhs] ...) (orig-id ...) body ...)
       (with-syntax ([(splicing-temp ...) (generate-temporaries #'(id ...))])
         #'(begin
             ;; Evaluate each RHS only once:
             (define-syntax splicing-temp rhs) ...
             ;; Partially expand `body' to push down `let-syntax':
             (expand-ssp-body (id ...) (splicing-temp ...) (orig-id ...) body)
             ...))]))

  (define-syntax (expand-ssp-body stx)
    (syntax-case stx ()
      [(_ (sp-id ...) (temp-id ...) (orig-id ...) body)
       (let ([ctx (syntax-local-make-definition-context #f #f)])
         (for ([sp-id (in-list (syntax->list #'(sp-id ...)))]
               [temp-id (in-list (syntax->list #'(temp-id ...)))])
           (syntax-local-bind-syntaxes (list sp-id)
                                       #`(syntax-local-value (quote-syntax #,temp-id))
                                       ctx))
         (let ([body (local-expand #'(force-expand body)
                                   (syntax-local-context)
                                   null ;; `force-expand' actually determines stopping places
                                   ctx)])
           (let ([body
                  ;; Extract expanded body out of `body':
                  (syntax-case body (quote)
                    [(quote body) #'body])])
             (syntax-case body ( begin
                                  define-values
                                  define-syntaxes
                                  begin-for-syntax
                                  module
                                  module*
                                  #%require
                                  #%provide
                                  #%declare )
               [(begin expr ...)
                (syntax/loc/props body
                  (begin (expand-ssp-body (sp-id ...) (temp-id ...) (orig-id ...) expr) ...))]
               [(define-values (id ...) rhs)
                (syntax/loc/props body
                  (define-values (id ...)
                    (letrec-syntaxes ([(sp-id) (syntax-local-value (quote-syntax temp-id))] ...)
                                     rhs)))]
               [(define-syntaxes ids rhs)
                (syntax/loc/props body
                  (define-syntaxes ids (wrap-param-et rhs (orig-id ...) (temp-id ...))))]
               [(begin-for-syntax e ...)
                (syntax/loc/props body
                  (begin-for-syntax (wrap-param-et e (orig-id ...) (temp-id ...)) ...))]
               [(module . _) body]
               [(module* name #f form ...)
                (datum->syntax body
                               (list #'module* #'name #f
                                     #`(expand-ssp-module-begin
                                        (sp-id ...) (temp-id ...) (orig-id ...)
                                        #,body name form ...))
                               body)]
               [(module* . _) body]
               [(#%require . _) body]
               [(#%provide . _) body]
               [(#%declare . _) body]
               [expr (syntax/loc body
                       (letrec-syntaxes ([(sp-id) (syntax-local-value (quote-syntax temp-id))] ...)
                                        expr))]))))]))

  (define-syntax (expand-ssp-module-begin stx)
    (syntax-case stx ()
      [(_ (sp-id ...) (temp-id ...) (orig-id ...) mod-form mod-name-id body-form ...)
       (unless (eq? (syntax-local-context) 'module-begin)
         (raise-syntax-error #f "only allowed in module-begin context" stx))
       (let ([ctx (syntax-local-make-definition-context #f #f)])
         (for ([sp-id (in-list (syntax->list #'(sp-id ...)))]
               [temp-id (in-list (syntax->list #'(temp-id ...)))])
           (syntax-local-bind-syntaxes (list sp-id)
                                       #`(syntax-local-value (quote-syntax #,temp-id))
                                       ctx))
         (let* ([forms (syntax->list #'(body-form ...))]
                ; emulate how the macroexpander expands module bodies and introduces #%module-begin
                [body (if (= (length forms) 1)
                          (let ([body (local-expand (car forms) 'module-begin #f ctx)])
                            (syntax-case body (#%plain-module-begin)
                              [(#%plain-module-begin . _) body]
                              [_ (datum->syntax #'mod-form (list '#%module-begin body) #'mod-form)]))
                          (datum->syntax #'mod-form (list* '#%module-begin forms) #'mod-form))]
                [body (syntax-property body 'enclosing-module-name (syntax-e #'mod-name-id))]
                [body (local-expand body 'module-begin #f ctx)])
           (syntax-case body (#%plain-module-begin)
             [(#%plain-module-begin form ...)
              (syntax/loc/props body
                (#%plain-module-begin
                 (expand-ssp-body (sp-id ...) (temp-id ...) (orig-id ...) form) ...))]
             [_ (raise-syntax-error
                 #f "expansion of #%module-begin is not a #%plain-module-begin form" body)])))]))

  (define-syntax (force-expand stx)
    (syntax-case stx ()
      [(_ stx)
       ;; Expand `stx' to reveal type of form, and then preserve it via
       ;; `quote':
       (syntax-property
        #`(quote #,(local-expand #'stx
                                 'module
                                 (kernel-form-identifier-list)
                                 #f))
        'certify-mode
        'transparent)]))

  (define-for-syntax (parameter-of id)
    (let ([sp (syntax-parameter-local-value id)])
      (syntax-parameter-target-parameter
       (syntax-parameter-target sp))))

  (begin-for-syntax
    (define-syntax (wrap-param-et stx)
      (syntax-case stx ()
        [(_ e (orig-id ...) (temp-id ...))
         (let ([as-expression
                (lambda ()
                  #'(parameterize ([(parameter-of (quote-syntax orig-id)) 
                                    (quote-syntax temp-id)]
                                   ...)
                      e))])
           (if (eq? (syntax-local-context) 'expression)
               (as-expression)
               (let ([e (local-expand #'e
                                      (syntax-local-context)
                                      (kernel-form-identifier-list)
                                      #f)])
                 (syntax-case e (begin
                                  define-syntaxes define-values
                                  begin-for-syntax
                                  module module*
                                  #%require #%provide #%declare
                                  quote-syntax)
                   [(begin form ...)
                    (syntax/loc/props e
                      (begin (wrap-param-et form (orig-id ...) (temp-id ...)) ...))]
                   [(define-syntaxes . _) e]
                   [(begin-for-syntax . _) e]
                   [(define-values ids rhs)
                    (syntax/loc/props e
                      (define-values ids (wrap-param-et rhs (orig-id ...) (temp-id ...))))]
                   [(module . _) e]
                   [(module* n #f form ...)
                    (datum->syntax
                     e
                     (syntax-e #'(module* n #f (wrap-param-et form (orig-id ...) (temp-id ...)) ...))
                     e
                     e)]
                   [(module* . _) e]
                   [(#%require . _) e]
                   [(#%provide . _) e]
                   [(#%declare . _) e]
                   [(quote-syntax . _) e]
                   [else (as-expression)]))))])))])
