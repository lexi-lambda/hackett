#lang hackett

(require hackett/private/test
         (only-in racket/base
           define-syntax for-syntax begin-for-syntax)
         (for-syntax racket/base
                     syntax/parse
                     (only-in hackett/private/prop-case-pattern-expander
                       case-pattern-expander)))

(begin-for-syntax
  (struct group [hash])
  (define (group-ref g x)
    (hash-ref (group-hash g) x)))

(define-syntax group-ref
  (case-pattern-expander
   (syntax-parser
     [(_ {~var G (static group? "group")} x)
      (group-ref (attribute G.value) (syntax-e #'x))])))

(data Result
  (Success Integer)
  (Failure String))

(define-syntax G (group (hash 'good #'Success 'bad #'Failure)))

(test {(case (Success 5)
         [((group-ref G good) x) (Just x)]
         [((group-ref G bad) y) Nothing])
       ==!
       (Just 5)})

(data T (C Integer Integer))

(define-syntax n
  (case-pattern-expander
   (syntax-parser
     [(n) #'m])))

(define-syntax m
  (case-pattern-expander
   (syntax-parser
     [:id #'C]
     [(_ . _)
      (raise-syntax-error #f "must use `m` as an identifier" this-syntax)])))

(test {(case (C 1 2)
         [((n) x y) x])
       ==!
       1})

