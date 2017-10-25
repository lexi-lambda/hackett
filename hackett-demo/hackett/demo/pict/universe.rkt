#lang hackett

(require (only-in racket/base all-from-out for-syntax module submod))

(module shared hackett
  (#%require/only-types hackett)
  (provide (data KeyEvent) (data MouseEvent))

  (data KeyEvent
    (ke:char String)
    ke:left ke:right ke:up ke:down
    ke:shift ke:rshift ke:control ke:rcontrol ke:escape
    ke:wheel-up ke:wheel-down ke:wheel-left ke:wheel-right
    (ke:function Integer)
    (ke:unknown String))

  (data MouseEvent
    me:button-down
    me:button-up
    me:drag
    me:move
    me:enter
    (me:unknown String)))

(module untyped racket/base
  (require hackett/private/util/require
           (only-in hackett/private/base unmangle-types-in)

           (prefix-in hackett: (unmangle-types-in #:prefix t:
                                                  (combine-in hackett
                                                              hackett/demo/pict
                                                              (submod ".." shared))))
           (postfix-in - (combine-in 2htdp/universe pict racket/base racket/match racket/promise))

           (only-in (unmangle-types-in #:prefix t: hackett)
                    : t:IO t:Unit
                    [t:∀ ∀] [t:-> ->] [t:Integer Integer] [t:Double Double])
           (only-in hackett/private/prim IO unsafe-run-io!)
           hackett/private/prim/type-provide
           threading)

  (provide (typed-out
            [random-integer : {Integer -> Integer -> (t:IO Integer)}]
            [random-double : (t:IO Double)]
            [animate : {{Integer -> hackett:t:Pict} -> (t:IO t:Unit)}]
            [big-bang/proc
             : (∀ [state]
                  {state
                   -> {state -> (t:IO state)} -> Double
                   -> {state -> hackett:t:Pict}
                   -> {hackett:t:KeyEvent -> state -> (t:IO state)}
                   -> {hackett:t:KeyEvent -> state -> (t:IO state)}
                   -> {Integer -> Integer -> hackett:t:MouseEvent -> state -> (t:IO state)}
                   -> (t:IO state)})]))

  (define (pict->image p) (pict->bitmap- (force- p)))

  (define (string->KeyEvent str)
    (match- str
      [(app string-length- (==- 1 =-)) (hackett:ke:char str)]
      [(regexp #px"^f(\\d+)$" (list _ (app string->number- n))) (hackett:ke:function n)]
      ["left" hackett:ke:left] ["right" hackett:ke:right]
      ["up" hackett:ke:up] ["down" hackett:ke:down]
      ["shift" hackett:ke:shift] ["rshift" hackett:ke:rshift]
      ["control" hackett:ke:control] ["rcontrol" hackett:ke:rcontrol]
      ["escape" hackett:ke:escape]
      ["wheel-up" hackett:ke:wheel-up] ["wheel-down" hackett:ke:wheel-down]
      ["wheel-left" hackett:ke:wheel-left] ["wheel-right" hackett:ke:wheel-right]
      [_ (hackett:ke:unknown str)]))

  (define (string->MouseEvent str)
    (match- str
      ["button-down" hackett:me:button-down] ["button-up" hackett:me:button-up]
      ["drag" hackett:me:drag] ["move" hackett:me:move] ["enter" hackett:me:enter]
      [_ (hackett:me:unknown str)]))

  (define ((random-integer low) high)
    (IO (λ- (rw) ((hackett:Tuple rw) (random- (force- low) (force- high))))))

  (define random-double
    (IO (λ- (rw) ((hackett:Tuple rw) (real->double-flonum- (random-))))))

  (define (animate f)
    (IO (λ- (rw)
          (animate- (λ- (x) (pict->image ((force- f) x))))
          ((hackett:Tuple rw) hackett:Unit))))

  (define (((((((big-bang/proc init-state)
                tick-fn) tick-rate)
              render-fn)
             key-fn)
            release-fn)
           mouse-fn)
    (IO (λ- (rw)
          ((hackett:Tuple rw)
           (big-bang- init-state
             [on-tick- (λ- (s) (force- (unsafe-run-io! ((force- tick-fn) s))))
                       (force- tick-rate)]
             [to-draw- (λ- (s) (pict->image ((force- render-fn) s)))]
             [on-key-
              (λ- (s str)
                (force- (unsafe-run-io! ((force- ((force- key-fn) (string->KeyEvent str))) s))))]
             [on-release-
              (λ- (s str)
                (force- (unsafe-run-io! ((force- ((force- release-fn) (string->KeyEvent str))) s))))]
             [on-mouse-
              (λ- (s x y str)
                  (~> mouse-fn
                      force-
                      (#%app x)
                      force-
                      (#%app y)
                      force-
                      (#%app (string->MouseEvent str))
                      force-
                      (#%app s)
                      unsafe-run-io!
                      force-))]))))))

(require (for-syntax racket/base)
         syntax/parse/define

         (submod "." shared)
         (submod "." untyped))

(provide (data KeyEvent) (data MouseEvent) animate big-bang
         random-integer random-double)

(define-syntax-parser big-bang
  [(_ init-state:expr
      {~or {~optional {~seq #:on-tick tick-fn:expr tick-rate:expr}
                      #:defaults ([tick-fn #'id] [tick-rate #'1.0])}
           {~once {~seq #:to-draw render-fn:expr}}
           {~optional {~seq #:on-key key-fn:expr}
                      #:defaults ([key-fn #'(λ [_ s] (pure s))])}
           {~optional {~seq #:on-release release-fn:expr}
                      #:defaults ([release-fn #'(λ [_ s] (pure s))])}
           {~optional {~seq #:on-mouse mouse-fn:expr}
                      #:defaults ([mouse-fn #'(λ [_ _ _ s] (pure s))])}}
      ...)
   #'(big-bang/proc init-state tick-fn tick-rate render-fn key-fn release-fn mouse-fn)])
