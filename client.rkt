#lang rascal

(data Bool true false)

(data (Maybe a)
      (just a)
      nothing)

(data (Tuple4 a b c d)
      (tuple4 a b c d))

(case true
  [true 1]
  [false 0])

(let ([from-maybe (λ (x y) (case y
                             [(just v) v]
                             [nothing x]))])
  (tuple4
   (from-maybe 0 (just 1))
   (from-maybe 0 nothing)
   (from-maybe "" (just "hello"))
   (from-maybe "" nothing)))
