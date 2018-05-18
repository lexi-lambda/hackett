#lang curly-fn racket/base

(require (for-syntax racket/base
                     racket/format
                     syntax/intdef
                     threading

                     hackett/private/infix
                     hackett/private/typecheck
                     hackett/private/util/stx)
         syntax/parse/define

         (only-in hackett/private/adt type-constructor-spec))

(provide type)

(begin-for-syntax
  ; Alias transformer bindings; use the make-alias-transformer constructor instead of creating
  ; instances of this struct directly.
  (struct alias-transformer (procedure fixity)
    #:property prop:procedure (struct-field-index procedure)
    #:property prop:infix-operator
    (λ (self) (alias-transformer-fixity self)))

  (define (make-alias-transformer args type-template fixity)
    (let ([arity (length args)])
      (alias-transformer
       (cond
         [(zero? arity)
          (make-variable-like-transformer type-template)]
         [else
          (syntax-parser
            [(head:id t:type ...)
             #:fail-unless (= (length (attribute t)) arity)
                           (~a "expected " arity " argument(s) to type alias, got "
                               (length (attribute t)))
             (for/fold ([result (insts type-template (map cons args (attribute t)))])
                       ([residual (in-list (attribute t.residual))])
               (syntax-track-origin result residual #'head))]
            [:id
             #:fail-when #t (~a "expected " arity " argument(s) to type alias")
             (error "unreachable")])])
       fixity))))


(define-syntax-parser type
  [(_ ctor-spec:type-constructor-spec {~type type-template:expr})
   #:with [ctor-spec*:type-constructor-spec] (type-namespace-introduce #'ctor-spec)
   #:with fixity (attribute ctor-spec.fixity)

   ; Create a dummy internal definition context with args.
   #:do [(define intdef-ctx (syntax-local-make-definition-context))
         (syntax-local-bind-syntaxes (attribute ctor-spec*.arg) #f intdef-ctx)]
   #:with [arg* ...] (map #{internal-definition-context-introduce intdef-ctx %}
                          (attribute ctor-spec*.arg))

   ; Expanding the type in `ctx` checks immediately that it is a valid type,
   ; rather than deferring that check to when the type alias is applied.
   #:with {~var type-template- (type intdef-ctx)} #'type-template
   (~>> #'(begin
            (define-values [] type-template-.residual)
            (define-syntax ctor-spec*.tag
              (make-alias-transformer
               (list (quote-syntax arg*) ...)
               (quote-syntax type-template-.expansion)
               'fixity)))
        (internal-definition-context-track intdef-ctx))])

