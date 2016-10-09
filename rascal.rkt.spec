#lang rascal

(data (Maybe a)
      Nothing
      (Just a))

(ann x Int)
(def x
  (let ([x 3]
        [y 7])
    {y + z}))

(class (Show a)
  [show {Int -> a -> String}])

(instance (Show a) => (Show (Maybe a))
  (def+ show
    [Nothing  -> "Nothing"]
    [(Just x) -> {"Just " <> (show x)}]))

; type annotations
; unary functions
; ADTs
; typeclasses
; number literals
; string literals
; parametric polymorphism
