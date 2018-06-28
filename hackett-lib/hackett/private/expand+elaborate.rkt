#lang racket/base

; This module implements Hackett’s multi-pass macroexpansion performed as part of elaboration. It does
; not actually implement any of the logic used to solve constraints; that functionality is implemented
; by other macros that cooperate with the elaborating expander.
;
; When a Hackett module expands, it is expanded in three passes:
;
;   1. First, an initial expansion pass expands macros that do not require elaboration. Macros that
;      require elaboration can request their expansion be deferred by expanding to a use of
;      (syntax-local-elaborate-defer-id).
;
;   2. Once the initial expansion pass completes, the expander begins the process of elaboration. All
;      macros that requested deferred expansion are re-expanded. If the macro can make progress, it
;      calls syntax-local-elaborate-did-make-progress!. If it still requires additional information
;      (which might be gathered while expanding other deferred macros), it calls
;      syntax-local-elaborate-did-defer! and expands again to a use of
;      (syntax-local-elaborate-defer-id).
;
;      After performing expansion, the elaborator checks whether or not any macros called
;      syntax-local-elaborate-did-make-progress! and syntax-local-elaborate-did-defer! during
;      elaboration. If both functions were called, the expander makes another elaboration pass.
;      Otherwise, elaboration is complete.
;
;   3. Finally, the elaborator performs a finalization pass. Macros cannot request to be deferred
;      during this pass, so they must either expand or raise an error.
;
; The reason for this complicated expansion process is that certain forms may wish to consume type
; information, and others may constrain type information. The most straightforward example of this
; behavior involves typeclasses: typeclasses require dictionary elaboration, and picking the
; appropriate dictionary requires fully-solved type information, but solving some constraints (that
; is, constraints with functional dependencies) may force some solver variables to unify. So we need
; to run the solver until we reach a fixpoint.

(require (for-template racket/base)
         racket/contract
         racket/format
         racket/list
         racket/match
         racket/syntax
         syntax/parse

         hackett/private/util/stx)

(provide (contract-out [syntax-local-elaborate-defer
                        (->* [syntax?] [#:did-defer!? any/c] syntax?)]
                       [local-expand+elaborate
                        (->* [syntax?] [(listof internal-definition-context?)] syntax?)]
                       [local-expand/defer-elaborate
                        (->* [syntax?
                              (or/c 'expression 'top-level 'module 'module-begin list?)
                              (listof identifier?)]
                             [(listof internal-definition-context?)]
                             syntax?)]
                       [make-elaborating-transformer
                        (->* [(-> syntax? syntax?)]
                             [#:allowed-passes (non-empty-listof elaborate-pass?)]
                             (-> syntax? syntax?))]
                       [syntax-local-elaborate-top
                        (-> syntax? syntax?)])
         elaborate-pass?
         syntax-local-elaborate-pass
         syntax-local-elaborating-with-defers?
         syntax-local-elaborate-defer-id
         syntax-local-elaborate-did-make-progress!
         syntax-local-elaborate-did-defer!)

(define elaborate-passes '(expand elaborate finalize))
(define (elaborate-pass? v) (and (memq v elaborate-passes) #t))
(define (elaboration-pass->string v)
  (match v
    ['expand "initial expansion"]
    ['elaborate "elaboration"]
    ['finalize "finalization"]))

(define current-syntax-elaborate-pass (make-parameter #f))
(define current-elaborate-did-make-progress? (make-parameter #f))
(define current-elaborate-did-defer? (make-parameter #f))
(define current-elaborate-defer-id (make-parameter #f))

(define (syntax-local-elaborate-pass) (current-syntax-elaborate-pass))
(define (syntax-local-elaborating-with-defers?)
  (memq (current-syntax-elaborate-pass) '(expand elaborate)))

(define (assert-elaborating! who [allowed-passes '(elaborate)])
  (unless (memq (current-syntax-elaborate-pass) allowed-passes)
    (raise-arguments-error who "not currently elaborating")))

(define (syntax-local-elaborate-defer-id #:did-defer!? [did-defer!? #f])
  (assert-elaborating! 'syntax-local-elaborate-defer-id '(expand elaborate))
  (when (and did-defer!? (eq? (current-syntax-elaborate-pass) 'elaborate))
    (syntax-local-elaborate-did-defer!))
  (current-elaborate-defer-id))

(define (syntax-local-elaborate-defer stx #:did-defer!? [did-defer!? #f])
  (assert-elaborating! 'syntax-local-elaborate-defer '(expand elaborate))
  (quasisyntax/loc stx
    (#,(replace-stx-loc (syntax-local-elaborate-defer-id #:did-defer!? did-defer!?) stx) #,stx)))

(define (syntax-local-elaborate-did-make-progress!)
  (assert-elaborating! 'syntax-local-elaborate-did-make-progress!)
  (current-elaborate-did-make-progress? #t))

(define (syntax-local-elaborate-did-defer!)
  (assert-elaborating! 'syntax-local-elaborate-did-defer!)
  (current-elaborate-did-defer? #t))

(define no-op-transformer (syntax-parser [(_ e) #'e]))

(define (local-expand+elaborate stx [intdef-ctxs '()])
  (define expand-context (syntax-local-context))

  (unless (or (eq? expand-context 'top-level)
              (eq? expand-context 'module-begin))
    (raise-arguments-error 'local-expand+elaborate "not in top level or module begin context"))
  (when (current-syntax-elaborate-pass)
    (raise-arguments-error 'local-expand+elaborate "already elaborating"))

  (let* ([intdef-ctx (syntax-local-make-definition-context #f #f)]
         [intdef-ctxs (cons intdef-ctx intdef-ctxs)])

    ; Each expansion pass needs a fresh defer binding so that subsequent expansions will expand macros
    ; deferred in the previous pass. By binding it to #%expression but putting it in the stop list
    ; during the expansion pass it’s introduced, it will be harmlessly expanded on subsequent passes,
    ; but stopped on for the current pass.
    (define (generate-defer-id)
      (let ([defer-id (generate-temporary '#%defer)])
        (syntax-local-bind-syntaxes (list (syntax-local-identifier-as-binding
                                           (syntax-local-introduce defer-id)))
                                    #'no-op-transformer
                                    intdef-ctx)
        (internal-definition-context-introduce intdef-ctx defer-id)))

    (define (expand stx)
      (let ([defer-id (generate-defer-id)])
        (parameterize ([current-syntax-elaborate-pass 'expand]
                       [current-elaborate-defer-id defer-id])
          (local-expand stx expand-context (list #'module* defer-id) intdef-ctxs
                        #:extend-stop-ids? #f))))

    (define (elaborate stx)
      (let ([defer-id (generate-defer-id)])
        (parameterize ([current-syntax-elaborate-pass 'elaborate]
                       [current-elaborate-did-make-progress? #f]
                       [current-elaborate-did-defer? #f]
                       [current-elaborate-defer-id defer-id])
          (values (local-expand stx expand-context (list #'module* defer-id) intdef-ctxs
                                #:extend-stop-ids? #f)
                  (current-elaborate-did-make-progress?)
                  (current-elaborate-did-defer?)))))

    (define (finalize stx)
      (parameterize ([current-syntax-elaborate-pass 'finalize])
        (local-expand stx expand-context (list #'module*) intdef-ctxs)))

    (let loop ([stx (expand stx)])
      (let-values ([[stx* did-make-progress? did-defer?] (elaborate stx)])
        (if (and did-make-progress? did-defer?)
            (loop stx*)
            (finalize stx*))))))

(define (local-expand/defer-elaborate stx context stop-list [intdef-ctxs '()])
  (let ([stop-list* (if (syntax-local-elaborating-with-defers?)
                        (cons (syntax-local-elaborate-defer-id) stop-list)
                        stop-list)])
    (local-expand stx context (cons #'module* stop-list*) intdef-ctxs #:extend-stop-ids? #f)))

(define (make-elaborating-transformer #:allowed-passes [allowed-passes elaborate-passes] proc)
  ; Trampoline to get into an expression context. This helps to avoid “not currently elaborating”
  ; failures triggered by partial expansion that could be trivially avoided by waiting a little bit
  ; longer to be expanded (which is relevant when expanding at the top level).
  (make-trampolining-expression-transformer
   (lambda (stx)
     (let ([allowed-passes (remove-duplicates allowed-passes eq?)]
           [this-pass (syntax-local-elaborate-pass)])
       (unless this-pass
         (raise-syntax-error #f "not currently elaborating" stx))

       (unless (memq this-pass allowed-passes)
         (raise-syntax-error
          #f
          (match allowed-passes
            [(list _ _)
             (~a "not allowed during " (elaboration-pass->string this-pass) " pass")]
            [(list allowed-pass)
             (~a "only allowed during " (elaboration-pass->string allowed-pass) " pass")])
          stx))

       (proc stx)))))

;; ---------------------------------------------------------------------------------------------------

; When expanding at the top level, we have to be especially careful about the order of expansion,
; since Racket needs to interleave expansion and evaluation of forms within a `begin` form. Therefore,
; Hackett’s #%top-interaction performs partial expansion prior to performing elaboration, but in rare
; cases, that partial expansion is the wrong thing. In those situations, macros can use
; syntax-local-elaborate-top to request that #%top-interaction switch from partial expansion to
; elaboration earlier than it otherwise would.

(module elaborate-top-transformer racket/base
  (require (for-syntax racket/base))
  (provide #%elaborate-top)
  (define-syntax (#%elaborate-top stx)
    (raise-syntax-error #f "not at top level" stx)))
(require (for-template 'elaborate-top-transformer))

(define (syntax-local-elaborate-top stx)
  (unless (eq? (syntax-local-context) 'top-level)
    (raise-arguments-error 'syntax-local-elaborate-top "not in top level context"))
  (quasisyntax/loc stx
    (#,(replace-stx-loc #'#%elaborate-top stx) #,stx)))
