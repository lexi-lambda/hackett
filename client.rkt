#lang rascal

;#|

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

;|#

;#|

(data (List a)
      (cons a (List a))
      nil)

(letrec ([flip : (∀ [a b c] (→ (→ a (→ b c))
                               (→ b (→ a c))))
               (λ (f x y) (f y x))]
         [foldl : (∀ [b a] (→ (→ b (→ a b)) (→ b (→ (List a) b))))
                (λ (f acc lst)
                  (case lst
                    [nil acc]
                    [(cons x xs) (foldl f (f acc x) xs)]))]
         [reverse : (∀ [a] (→ (List a) (List a)))
                  (foldl (flip cons) nil)])
  (reverse (cons 1 (cons 2 nil))))

;|#
