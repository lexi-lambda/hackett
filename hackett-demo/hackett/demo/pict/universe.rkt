#lang hackett

(require (only-in racket/base all-from-out for-syntax module submod))

(module shared hackett
  (#%require/only-types hackett)
  (provide (data Key-Event) (data Mouse-Event))

  (data Key-Event
    (KE:Char String)
    KE:Left KE:Right KE:Up KE:Down
    KE:Shift KE:Rshift KE:Control KE:R-Control KE:Escape
    KE:Wheel-Up KE:Wheel-Down KE:Wheel-Left KE:Wheel-Right
    (KE:Function Integer)
    (KE:Unknown String))

  (data Mouse-Event
    ME:Button-Down
    ME:Button-Up
    ME:Drag
    ME:Move
    ME:Enter
    (ME:Unknown String)))

(module untyped racket/base
  (require hackett/private/type-reqprov
           hackett/private/util/require

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
                   -> {hackett:t:Key-Event -> state -> (t:IO state)}
                   -> {hackett:t:Key-Event -> state -> (t:IO state)}
                   -> {Integer -> Integer -> hackett:t:Mouse-Event -> state -> (t:IO state)}
                   -> (t:IO state)})]))

  (define (pict->image p) (pict->bitmap- (force- p)))

  (define (string->Key-Event str)
    (match- str
      [(app string-length- (==- 1 =-)) (hackett:KE:Char str)]
      [(regexp #px"^f(\\d+)$" (list _ (app string->number- n))) (hackett:KE:Function n)]
      ["left" hackett:KE:Left] ["right" hackett:KE:Right]
      ["up" hackett:KE:Up] ["down" hackett:KE:Down]
      ["shift" hackett:KE:Shift] ["rshift" hackett:KE:Rshift]
      ["control" hackett:KE:Control] ["rcontrol" hackett:KE:R-Control]
      ["escape" hackett:KE:Escape]
      ["wheel-up" hackett:KE:Wheel-Up] ["wheel-down" hackett:KE:Wheel-Down]
      ["wheel-left" hackett:KE:Wheel-Left] ["wheel-right" hackett:KE:Wheel-Right]
      [_ (hackett:KE:Unknown str)]))

  (define (string->Mouse-Event str)
    (match- str
      ["button-down" hackett:ME:Button-Down] ["button-up" hackett:ME:Button-Up]
      ["drag" hackett:ME:Drag] ["move" hackett:ME:Move] ["enter" hackett:ME:Enter]
      [_ (hackett:ME:Unknown str)]))

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
                (force- (unsafe-run-io! ((force- ((force- key-fn) (string->Key-Event str))) s))))]
             [on-release-
              (λ- (s str)
                (force- (unsafe-run-io! ((force- ((force- release-fn) (string->Key-Event str))) s))))]
             [on-mouse-
              (λ- (s x y str)
                  (~> mouse-fn
                      force-
                      (#%app x)
                      force-
                      (#%app y)
                      force-
                      (#%app (string->Mouse-Event str))
                      force-
                      (#%app s)
                      unsafe-run-io!
                      force-))]))))))

(require (for-syntax racket/base)
         syntax/parse/define

         (submod "." shared)
         (submod "." untyped))

(provide (data Key-Event) (data Mouse-Event) animate big-bang
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
