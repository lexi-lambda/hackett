#lang hackett

(require (only-in racket/base all-from-out module submod))

(module shared hackett
  (provide (data Color) color-red color-green color-blue color-alpha
           red orange yellow green blue purple)

  (data Color (color Integer Integer Integer Double))
  (defn color-red : {Color -> Integer} [[(color x _ _ _)] x])
  (defn color-green : {Color -> Integer} [[(color _ x _ _)] x])
  (defn color-blue : {Color -> Integer} [[(color _ _ x _)] x])
  (defn color-alpha : {Color -> Double} [[(color _ _ _ x)] x])

  (def red : Color (color 255 0 0 1.0))
  (def orange : Color (color 255 165 0 1.0))
  (def yellow : Color (color 255 255 0 1.0))
  (def green : Color (color 0 255 0 1.0))
  (def blue : Color (color 0 0 255 1.0))
  (def purple : Color (color 128 0 128 1.0)))

(module untyped racket/base
  (require hackett/private/util/require

           (prefix-in hackett: (combine-in hackett (submod ".." shared)))
           (postfix-in - (combine-in pict racket/base racket/draw racket/promise))

           (only-in hackett : -> Integer Double String IO Unit)
           (only-in hackett/private/base define-base-type)
           (only-in hackett/private/prim/type io)
           hackett/private/prim/type-provide)

  (define-base-type Pict)

  (provide Pict
           (typed-out
            [pict-width : {Pict -> Double}]
            [pict-height : {Pict -> Double}]
            [pict-ascent : {Pict -> Double}]
            [pict-descent : {Pict -> Double}]

            [blank : Pict]
            [blank-square : {Double -> Pict}]
            [blank-rect : {Double -> Double -> Pict}]

            [text : {Integer -> String -> Pict}]

            [frame : {Pict -> Pict}]

            [ellipse : {Double -> Double -> Pict}]
            [circle : {Double -> Pict}]
            [filled-ellipse : {Double -> Double -> Pict}]
            [filled-circle : {Double -> Pict}]

            [rectangle : {Double -> Double -> Pict}]
            [square : {Double -> Pict}]
            [filled-rectangle : {Double -> Double -> Pict}]
            [filled-square : {Double -> Pict}]

            [rounded-rectangle : {Double -> Double -> Double -> Pict}]
            [rounded-square : {Double -> Double -> Pict}]
            [filled-rounded-rectangle : {Double -> Double -> Double -> Pict}]
            [filled-rounded-square : {Double -> Double -> Pict}]

            [vl-append : {Pict -> Pict -> Pict}]
            [vc-append : {Pict -> Pict -> Pict}]
            [vr-append : {Pict -> Pict -> Pict}]
            [ht-append : {Pict -> Pict -> Pict}]
            [htl-append : {Pict -> Pict -> Pict}]
            [hc-append : {Pict -> Pict -> Pict}]
            [hbl-append : {Pict -> Pict -> Pict}]
            [hb-append : {Pict -> Pict -> Pict}]

            [scale : {Double -> Pict -> Pict}]
            [scale* : {Double -> Double -> Pict -> Pict}]

            [colorize : {hackett:Color -> Pict -> Pict}]

            [freeze : {Pict -> Pict}]

            [print-pict : {Pict -> (IO Unit)}]))

  (define (Color->color% c)
    (make-color- (force- (hackett:color-red c))
                 (force- (hackett:color-green c))
                 (force- (hackett:color-blue c))
                 (force- (hackett:color-alpha c))))

  (define (pict-width p) (real->double-flonum- (pict-width- (force- p))))
  (define (pict-height p) (real->double-flonum- (pict-height- (force- p))))
  (define (pict-ascent p) (real->double-flonum- (pict-ascent- (force- p))))
  (define (pict-descent p) (real->double-flonum- (pict-descent- (force- p))))

  (define blank (blank-))
  (define (blank-square x) (blank- (force- x)))
  (define ((blank-rect w) h) (blank- (force- w) (force- h)))

  (define ((text size) content) (text- (force- content) null- (force- size)))

  (define (frame pict) (frame- (force- pict)))

  (define ((ellipse w) h) (ellipse- (force- w) (force- h)))
  (define (circle d) (circle- (force- d)))
  (define ((filled-ellipse w) h) (filled-ellipse- (force- w) (force- h) #:draw-border? #f))
  (define (filled-circle d) (disk- (force- d) #:draw-border? #f))

  (define ((rectangle w) h) (rectangle- (force- w) (force- h)))
  (define (square s) (rectangle- (force- s) (force- s)))
  (define ((filled-rectangle w) h) (filled-rectangle- (force- w) (force- h)))
  (define (filled-square s) (filled-rectangle- (force- s) (force- s) #:draw-border? #f))

  (define (((rounded-rectangle r) w) h) (rounded-rectangle- (force- w) (force- h) (force- r)))
  (define ((rounded-square r) s) (rounded-rectangle- (force- s) (force- s) (force- r)))
  (define (((filled-rounded-rectangle r) w) h)
    (filled-rounded-rectangle- (force- w) (force- h) (force- r) #:draw-border? #f))
  (define ((filled-rounded-square r) s)
    (filled-rounded-rectangle- (force- s) (force- s) (force- r) #:draw-border? #f))

  (define ((vl-append x) y) (vl-append- (force- x) (force- y)))
  (define ((vc-append x) y) (vc-append- (force- x) (force- y)))
  (define ((vr-append x) y) (vr-append- (force- x) (force- y)))
  (define ((ht-append x) y) (ht-append- (force- x) (force- y)))
  (define ((htl-append x) y) (htl-append- (force- x) (force- y)))
  (define ((hc-append x) y) (hc-append- (force- x) (force- y)))
  (define ((hbl-append x) y) (hbl-append- (force- x) (force- y)))
  (define ((hb-append x) y) (hb-append- (force- x) (force- y)))

  (define ((scale x) p) (scale- (force- p) (force- x)))
  (define (((scale* w) h) p) (scale- (force- p) (force- w) (force- h)))

  (define ((colorize c) p) (colorize- (force- p) (Color->color% c)))

  (define (freeze p) (freeze- (force- p)))

  (define (print-pict p)
    (io (λ (rw)
          (println (force- p))
          ((hackett:tuple rw) hackett:unit)))))

(require (submod "." shared)
         (submod "." untyped))

(provide (all-from-out (submod "." shared))
         (all-from-out (submod "." untyped)))
