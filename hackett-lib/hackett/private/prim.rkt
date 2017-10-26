#lang racket/base

(require hackett/private/util/require

         (for-syntax racket/base)
         (postfix-in - (combine-in racket/base racket/promise))
         syntax/parse/define
         (only-in hackett/private/kernel module+ [#%app @%app])

         hackett/private/prim/base
         hackett/private/prim/op
         hackett/private/prim/type)

(provide (all-from-out hackett/private/prim/base)
         (all-from-out hackett/private/prim/op)
         (all-from-out hackett/private/prim/type)

         main)

(define-syntax-parser main
  [(_ e:expr)
   (datum->syntax this-syntax
                  (list #'module+ #'main #'(void- (force- (@%app unsafe-run-io! e))))
                  this-syntax)])
