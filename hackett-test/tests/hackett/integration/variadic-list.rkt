#lang hackett
(require hackett/private/test)

(def my-empty : (forall [a] (List a)) (List))

(defn last : (forall [a] {(List a) -> a})
  [[(List)]    (error! "last of empty list")]
  [[(List x)]  x]
  [[{x :: xs}] (last xs)])

(test {(List 1 2 3) ==! {1 :: 2 :: 3 :: Nil}})
(test {(head! (last (List (List 8 9) (List 10 100)))) ==! 10})
