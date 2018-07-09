#lang hackett/base

(require (only-in racket/base define-syntax for-syntax)
         (for-syntax racket/base
                     syntax/srcloc
                     hackett/private/typecheck)
         syntax/parse/define

         hackett/private/deferred-transformer
         (only-in hackett/private/prim error!))

(provide todo!)

(define-syntax todo!
  (make-expected-type-transformer
   (syntax-parser
     [(_ e ...)
      (let* ([type-str (type->string (get-expected this-syntax))]
             [message (string-append (source-location->prefix this-syntax)
                                     "todo! with type "
                                     type-str)])
        (syntax-property (quasisyntax/loc this-syntax (error! #,message))
                         'todo `#s(todo-item ,type-str ,type-str)))])))
