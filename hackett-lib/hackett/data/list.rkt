#lang hackett/private/kernel

(require (except-in hackett/private/adt data)
         hackett/data/maybe
         hackett/private/prim
         hackett/private/provide)

(provide (data List) head tail head! tail! take zip-with)

(defn head : (∀ [a] {(List a) -> (Maybe a)})
  [[{x :: _}] (just x)]
  [[nil     ] nothing])

(defn tail : (∀ [a] {(List a) -> (Maybe (List a))})
  [[{_ :: xs}] (just xs)]
  [[nil      ] nothing])

(defn head! : (∀ [a] {(List a) -> a})
  [[xs] (from-maybe (error! "head!: empty list") (head xs))])

(defn tail! : (∀ [a] {(List a) -> (List a)})
  [[xs] (from-maybe (error! "tail!: empty list") (tail xs))])

(defn take : (∀ [a] {Integer -> (List a) -> (List a)})
  [[n {x :: xs}]
   (if {n == 0}
       nil
       {x :: (take {n - 1} xs)})]
  [[_ nil]
   nil])

(defn zip-with : (∀ [a b c] {{a -> b -> c} -> (List a) -> (List b) -> (List c)})
  [[f {x :: xs} {y :: ys}] {(f x y) :: (zip-with f xs ys)}]
  [[_ _         _        ] nil])
