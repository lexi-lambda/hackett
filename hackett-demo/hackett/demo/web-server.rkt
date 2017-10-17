#lang hackett

(require (only-in racket/base submod for-syntax begin-for-syntax module)
         (for-syntax racket/base
                     racket/list
                     racket/syntax
                     syntax/parse/experimental/template)
         (only-in hackett/private/base type)
         syntax/parse/define)

; These datatypes are needed by both the untyped bindings and the typed code, so we need to put them
; in a a common submodule that can be imported by both.
(module shared hackett
  (#%require/only-types hackett)
  (provide (data Request) (data Response) response-status response-body)
  (data Request (request String))
  (data Response (response Integer String))

  (def response-status (λ [(response status _)] status))
  (def response-body (λ [(response _ body)] body)))

; This module implements some very simple bindings to the Racket web server than can be called from
; typed code. It provides a single binding, run-server, which just binds the web server to a port and
; passes a request to a callback function for every request. The callback should produce a response,
; which contains a response body and a status code.
(module untyped racket/base
  (require (only-in hackett/private/base unmangle-types-in)
           (prefix-in hackett: (unmangle-types-in #:no-introduce
                                                  (combine-in hackett (submod ".." shared))))
           (only-in (unmangle-types-in #:no-introduce hackett) : -> Integer String IO Unit)
           hackett/private/prim/type-provide
           (only-in hackett/private/prim/type io)
           racket/string
           racket/promise
           net/url-structs
           web-server/http/request-structs
           web-server/http/response-structs
           web-server/servlet-env)

  (provide (typed-out [run-server : {Integer -> {hackett:Request -> hackett:Response} -> (IO Unit)}]))

  (define (req->Request req)
    (hackett:request (string-join (map path/param-path (url-path (request-uri req))) "/")))

  (define ((run-server port) handler)
    (io (λ (rw)
          (serve/servlet
           #:port port
           #:launch-browser? #f
           #:banner? #f
           #:servlet-regexp #rx""
           (λ (req)
             (let ([res (handler (req->Request req))])
               (response/output
                #:code (force (hackett:response-status res))
                #:mime-type #"text/plain; charset=utf-8"
                (λ (out) (displayln (force (hackett:response-body res)) out))))))
          ((hackett:tuple rw) hackett:unit)))))

;; ---------------------------------------------------------------------------------------------------

(require (submod "." shared)
         (prefix-in racket: (submod "." untyped)))

(provide (class Param->) (class ->Body) defserver)

(defn request->path-segments : {Request -> (List String)}
  [[(request "")] {"" :: nil}]
  [[(request path)] (string-split "/" path)])

(class (Param-> a)
  [param-> : {String -> a}])

(instance (Param-> String)
  [param-> id])

(class (->Body a)
  [->body : {a -> String}])

(instance (->Body String)
  [->body id])

(instance (->Body Integer)
  [->body show])

(begin-for-syntax
  (define-syntax-class route-segment
    #:description "route segment"
    #:attributes [pat [var 1] [type 1]]
    #:commit
    [pattern pat:str
             #:attr [var 1] '()
             #:attr [type 1] '()]
    [pattern t:type
             #:attr pat (generate-temporary #'t)
             #:attr [var 1] (list #'pat)
             #:attr [type 1] (list #'t)])

  (define-syntax-class route-clause
    #:description "route"
    #:attributes [case-clause]
    #:literals [-> =>]
    [pattern [{~or GET POST}
              {~seq segment:route-segment ->} ...
              result:type
              => handler:expr]
             #:with handler-type (foldr (λ [x y] #`(-> #,x #,y)) #'result
                                        (append* (attribute segment.type)))
             #:with handler-annotated #'(: handler handler-type)
             #:with handler-expr (if (empty? (append* (attribute segment.var)))
                                     #'handler-annotated
                                     #'(handler-annotated (param-> segment.var) ... ...))
             #:attr case-clause (template [{{?@ segment.pat ::} ... nil}
                                           (response 200 (->body handler-expr))])]))

(define-syntax-parser defserver
  #:literals [-> =>]
  #:datum-literals [GET POST]
  [(_ run-id:id clause:route-clause ...)
   (template
    (defn run-id : {Integer -> (IO Unit)}
      [[port] (racket:run-server
               port (λ [req]
                      (case (request->path-segments req)
                        clause.case-clause ...
                        [_ (response 404 "Not Found")])))]))])
