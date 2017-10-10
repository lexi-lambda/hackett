#lang hackett/base

(require hackett/private/prim)

(provide (data Either) either is-left is-right lefts rights partition-eithers)

(defn either : (∀ [a b c] {{a -> c} -> {b -> c} -> (Either a b) -> c})
  [[f _ (left  x)] (f x)]
  [[_ g (right y)] (g y)])

(defn is-left : (forall [l r] {(Either l r) -> Bool})
  [[(left _)]  true]
  [[(right _)] false])

(defn is-right : (forall [l r] {(Either l r) -> Bool})
  [[(left _)]  false]
  [[(right _)] true])

(defn lefts : (forall [l r] {(List (Either l r)) -> (List l)})
  [[{e :: es}] (case e
                 [(left x) {x :: (lefts es)}]
                 [_        (lefts es)])]
  [[nil] nil])

(defn rights : (forall [l r] {(List (Either l r)) -> (List r)})
  [[{e :: es}] (case e
                 [(right x) {x :: (rights es)}]
                 [_         (rights es)])]
  [[nil] nil])

(def partition-eithers : (forall [l r] {(List (Either l r)) -> (Tuple (List l) (List r))})
  (foldr (λ* [[(left x)  (tuple ls rs)] (tuple {x :: ls} rs)]
             [[(right x) (tuple ls rs)] (tuple ls {x :: rs})])
         (tuple nil nil)))