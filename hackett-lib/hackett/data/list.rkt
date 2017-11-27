#lang hackett/base

(require hackett/data/maybe
         hackett/private/prim)

(provide (data List) head last tail init head! last! tail! init! uncons uncons! unfoldr nil? length
         nth nth! find-index index-of take take-while drop drop-while tails inits filter find
         foldr foldl reverse zip-with zip sum product iterate repeat replicate cycle! concat-map
         or and any? all? elem? not-elem? delete delete-by intersperse)

(defn head : (∀ [a] {(List a) -> (Maybe a)})
  [[{x :: _}] (Just x)]
  [[Nil     ] Nothing])

(defn last : (forall [a] {(List a) -> (Maybe a)})
  [[{x :: Nil}] (Just x)]
  [[{_ :: xs} ] (last xs)]
  [[_         ] Nothing])

(defn tail : (∀ [a] {(List a) -> (Maybe (List a))})
  [[{_ :: xs}] (Just xs)]
  [[Nil      ] Nothing])

(defn init : (forall [a] {(List a) -> (Maybe (List a))})
  [[Nil] Nothing]
  [[xs ] (Just (init! xs))])

(defn head! : (∀ [a] {(List a) -> a})
  [[xs] (from-maybe (error! "head!: empty list") (head xs))])

(defn last! : (forall [a] {(List a) -> a})
  [[xs] (from-maybe (error! "last!: empty list") (last xs))])

(defn tail! : (∀ [a] {(List a) -> (List a)})
  [[xs] (from-maybe (error! "tail!: empty list") (tail xs))])

(defn init! : (forall [a] {(List a) -> (List a)})
  [[{_ :: Nil}] Nil]
  [[{x :: xs} ] {x :: (init! xs)}]
  [[Nil       ] (error! "tail!: empty list")])

(defn uncons : (forall [a] {(List a) -> (Maybe (Tuple a (List a)))})
  [[{x :: xs}] (Just (Tuple x xs))]
  [[Nil      ] Nothing])

(defn uncons! : (forall [a] {(List a) -> (Tuple a (List a))})
  [[xs] (from-maybe (error! "uncons!: empty list") (uncons xs))])

(defn unfoldr : (forall [a b] {{b -> (Maybe (Tuple a b))} -> b -> (List a)})
  [[step seed] (case (step seed)
                 [Nothing            Nil]
                 [(Just (Tuple a b)) {a :: (unfoldr step b)}])])

(defn nil? : (forall [a] {(List a) -> Bool})
  [[Nil] True]
  [[_  ] False])

(def length : (forall [a] {(List a) -> Integer})
  (foldr (λ [_ acc] {acc + 1}) 0))

(defn nth : (forall [a] {(List a) -> Integer -> (Maybe a)})
  [[{x :: xs} n] (if {n < 0} Nothing
                     (if {n == 0} (Just x)
                         (nth xs {n - 1})))]
  [[Nil       _] Nothing])

(defn nth! : (forall [a] {(List a) -> Integer -> a})
  [[xs n] (from-maybe (error! "nth!: empty list") (nth xs n))])

(defn find-index : (forall [a] {{a -> Bool} -> (List a) -> (Maybe Integer)})
  [[p {x :: xs}] (if (p x) (Just 0) (map (+ 1) (find-index p xs)))]
  [[_ Nil      ] Nothing])

(def index-of : (forall [a] (Eq a) => {a -> (List a) -> (Maybe Integer)})
  {find-index . ==})

(defn take : (∀ [a] {Integer -> (List a) -> (List a)})
  [[n {x :: xs}]
   (if {n == 0}
       Nil
       {x :: (take {n - 1} xs)})]
  [[_ Nil]
   Nil])

(defn take-while : (∀ [a] {{a -> Bool} -> (List a) -> (List a)})
  [[p {x :: xs}]
   (if (p x)
       {x :: (take-while p xs)}
       Nil)]
  [[_ Nil]
   Nil])

(defn drop : (∀ [a] {Integer -> (List a) -> (List a)})
  [[n {x :: xs}]
   (if {n == 0}
       {x :: xs}
       (drop {n - 1} xs))]
  [[_ Nil]
   Nil])

(defn drop-while : (∀ [a] {{a -> Bool} -> (List a) -> (List a)})
  [[p {x :: xs}]
   (if (p x)
       (drop-while p xs)
       xs)]
  [[_ Nil]
   Nil])

(defn tails : (forall [a] {(List a) -> (List (List a))})
  [[{x :: xs}] {{x :: xs} :: (tails xs)}]
  [[Nil      ] Nil])

(defn inits : (forall [a] {(List a) -> (List (List a))})
  [[{x :: xs}] {(init! {x :: xs}) :: (inits xs)}]
  [[Nil      ] Nil])

(defn filter : (∀ [a] {{a -> Bool} -> (List a) -> (List a)})
  [[f {x :: xs}] (let ([ys (filter f xs)]) (if (f x) {x :: ys} ys))]
  [[_ Nil      ] Nil])

(defn find : (forall [a] {{a -> Bool} -> (List a) -> (Maybe a)})
  [[p {x :: xs}] (if (p x) (Just x) (find p xs))]
  [[p Nil      ] Nothing])

(defn foldl : (∀ [a b] {{b -> a -> b} -> b -> (List a) -> b})
  [[f a {x :: xs}] (let ([b (f a x)]) {b seq (foldl f b xs)})]
  [[_ a Nil      ] a])

(def reverse : (∀ [a] {(List a) -> (List a)})
  (foldl (flip ::) Nil))

(defn zip-with : (∀ [a b c] {{a -> b -> c} -> (List a) -> (List b) -> (List c)})
  [[f {x :: xs} {y :: ys}] {(f x y) :: (zip-with f xs ys)}]
  [[_ _         _        ] Nil])

(def zip : (∀ [a b] {(List a) -> (List b) -> (List (Tuple a b))})
  (zip-with Tuple))

(def sum : {(List Integer) -> Integer}
  (foldl + 0))

(def product : {(List Integer) -> Integer}
  (foldl * 1))

(defn iterate : (forall [a] {{a -> a} -> a -> (List a)})
  [[f x] {(f x) :: (iterate f (f x))}])

(defn repeat : (∀ [a] {a -> (List a)})
  [[x] (letrec ([xs {x :: xs}]) xs)])

(defn replicate : (∀ [a] {Integer -> a -> (List a)})
  [[n x] (if {n <= 0}
             Nil
             {x :: (replicate {n - 1} x)})])

(defn cycle! : (∀ [a] {(List a) -> (List a)})
  [[Nil] (error! "cycle!: empty list")]
  [[xs ] (letrec ([ys {xs ++ ys}]) ys)])

(def concat-map : (forall [a b] {{a -> (List b)} -> (List a) -> (List b)})
  =<<)

(def or : {(List Bool) -> Bool}
  (foldr || False))

(def and : {(List Bool) -> Bool}
  (foldr && True))

(defn any? : (∀ [a] {{a -> Bool} -> (List a) -> Bool})
  [[f] {or . (map f)}])

(defn all? : (∀ [a] {{a -> Bool} -> (List a) -> Bool})
  [[f] {and . (map f)}])

(defn elem? : (∀ [a] (Eq a) => {a -> (List a) -> Bool})
  [[x] (any? (== x))])

(defn not-elem? : (∀ [a] (Eq a) => {a -> (List a) -> Bool})
  [[x] {not . (elem? x)}])

(def delete : (∀ [a] (Eq a) => {a -> (List a) -> (List a)})
  (delete-by ==))

(defn delete-by : (∀ [a] {{a -> a -> Bool} -> a -> (List a) -> (List a)})
  [[=? x {y :: ys}]
   (if {y =? x}
       ys
       {y :: (delete-by =? x ys)})]
  [[_ _ Nil]
   Nil])

(defn intersperse : (forall [a] {a -> (List a) -> (List a)})
  [[_  Nil      ] Nil]
  [[in {x :: xs}] (letrec ([helper
                            (λ* [[{y :: ys}] {in :: y :: (helper ys)}]
                                [[Nil      ] Nil])])
                          {x :: (helper xs)})])
