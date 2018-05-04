#lang hackett

(require hackett/private/test)

(defn fold-map : (forall [a b] (Monoid b) => {{a -> b} -> (List a) -> b})
  [[_ Nil] mempty]
  [[f {x :: xs}] {(f x) ++ (fold-map f xs)}])

(test {(fold-map reverse {{1 :: 2 :: Nil} :: {3 :: 4 :: Nil} :: Nil}) ==! {2 :: 1 :: 4 :: 3 :: Nil}})
