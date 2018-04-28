#lang hackett/base

(require hackett/private/prim)

(provide (data Either) either is-left is-right lefts rights partition-eithers)

(defn either : (forall [a b c] {{a -> c} -> {b -> c} -> (Either a b) -> c})
  [[f _ (Left  x)] (f x)]
  [[_ g (Right y)] (g y)])

(defn is-left : (forall [l r] {(Either l r) -> Bool})
  [[(Left _)]  True]
  [[(Right _)] False])

(defn is-right : (forall [l r] {(Either l r) -> Bool})
  [[(Left _)]  False]
  [[(Right _)] True])

(defn lefts : (forall [l r] {(List (Either l r)) -> (List l)})
  [[{e :: es}] (case e
                 [(Left x) {x :: (lefts es)}]
                 [_        (lefts es)])]
  [[Nil] Nil])

(defn rights : (forall [l r] {(List (Either l r)) -> (List r)})
  [[{e :: es}] (case e
                 [(Right x) {x :: (rights es)}]
                 [_         (rights es)])]
  [[Nil] Nil])

(def partition-eithers : (forall [l r] {(List (Either l r)) -> (Tuple (List l) (List r))})
  (foldr (λ* [[(Left x)  (Tuple ls rs)] (Tuple {x :: ls} rs)]
             [[(Right x) (Tuple ls rs)] (Tuple ls {x :: rs})])
         (Tuple Nil Nil)))
