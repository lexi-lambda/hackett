#lang hackett

(require hackett/private/test)

(def fibs
  {0 :: 1 :: (zip-with + fibs (tail! fibs))})

(defn n-fibs
  [[n] (take n fibs)])

(test {(n-fibs 8) ==! {0 :: 1 :: 1 :: 2 :: 3 :: 5 :: 8 :: 13 :: Nil}})
