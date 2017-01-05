#lang racket/base

(require rackunit
         hackett/private/type
         syntax/id-table)

(define-base-type → #:arity 2)
(define-base-type List #:arity 1)
    
(let ([α (τvar #'α)]
      [β (τvar #'β)]
      [t1 (τvar #'t1)]
      [t2 (τvar #'t2)]
      [t3 (τvar #'t3)]
      [ω (τvar #'ω)])
  (check-equal? (free-id-table-ref
                 (solve-constraints
                  (list (τ~ t1 (→ (List β) t2) #f)
                        (τ~ (→ (List α) (→ (List α) (List α))) (→ t3 t1) #f)
                        (τ~ ω (→ t3 t2) #f)))
                 (τvar-id ω))
                (→ (List β) (List β))))
