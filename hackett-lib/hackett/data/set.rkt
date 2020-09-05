#lang hackett

(require hackett/data/ord)

(provide (data Set) ;; should put this in an internal thing but providing it for writing instances
         (data Triple)
         ;; query
         null
         size
         member
         not-member
         lookupLT
         lookupGT
         lookupLE
         lookupGE
         ;; construction
         empty
         singleton
         ;; insertion, deletion
         insert
         insertR
         delete
         ;; subset
         isProperSubsetOf?
         isSubsetOf?
         ;; disjoint
         disjoint
         ;; minimal, maximal
         lookupMin
         findMin
         lookupMax
         findMax
         deleteMin
         deleteMax
         ;; union
         unions
         union
         ;; difference
         difference
         ;; intersection
         intersection
         ;; filter
         set-filter
         partition
         ;; map
         set-map
         mapMonotonic
         ;; fold
         set-foldr
         set-foldl
         ;; lists
         toAscList
         toList
         fromList
         toDescList
         fromAscList
         fromDescList
         fromDistinctAscList
         fromDistinctDescList
         ;; list variations
         elems
         ;; split
         split
         splitS
         splitMember
         ;; indexing
         findIndex
         lookupIndex
         elemAt
         deleteAt
         take
         drop
         splitAt
         takeWhileAntitone
         dropWhileAntitone
         spanAntitone
         ;;
         deleteFindMin
         deleteFindMax
         minView
         maxView
         ;; link
         link
         insertMax
         insertMin
         ;; merge
         merge
         ;; utilities
         splitRoot
         powerSet
         cartesianProduct
         (data MergeSet)
         disjointUnion
         ;; debugging
         showTree
         ;; assertions
         valid
         ordered
         balanced
         validsize)
         

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I believe these are a part of the `Bits` typeclass in Haskell

(defn shiftL : {Integer -> Integer -> Integer}
  [[x n]
   (if {n == 0}
       x
       (shiftL {x * 2} {n - 1}))])

(defn shiftR : {Integer -> Integer -> Integer}
  [[x n]
   (if {n == 0}
       x
       (shiftR (quotient! x 2) {n - 1}))])

(def concat (foldr ++ ""))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Triples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(data (Triple A B C)
      (Triple A B C))

(instance (∀ [A B C] (Eq A) (Eq B) (Eq C) => (Eq (Triple A B C)))
  [== (λ* [[(Triple a1 b1 c1) (Triple a2 b2 c2)]
           {{a1 == a2} && {b1 == b2} && {c1 == c2}}])])

(instance (∀ [A B C] (Show A) (Show B) (Show C) => (Show (Triple A B C)))
  [show (λ* [[(Triple a b c)]
             {"Triple " ++ (show a) ++ " " ++ (show b) ++ " " ++ (show c)}])])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Set Datatype and Instances

(data (Set A)
      (Bin Integer A (Set A) (Set A))
      Tip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Eq converts the set to a list. In a lazy setting, this
;;  actually seems one of the faster methods to compare two trees
;;  and it is certainly the simplest :-)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(instance (∀ [A] (Eq A) => (Eq (Set A)))
  [== (λ* [[t1 t2]
           {{(size t1) == (size t2)} && {(toAscList t1) == (toAscList t2)}}])])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Ord
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(instance (∀ [A] (Ord A) => (Ord (Set A)))
  [compare (λ [s1 s2] (compare (toAscList s1) (toAscList s2)))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Show
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(instance (∀ [A] (Show A) => (Show (Set A)))
  [show (λ [s] {"fromList " ++ (show (toList s))})])

(instance (∀ [A] (Ord A) => (Semigroup (Set A)))
  [++ union])

(instance (∀ [A] (Ord A) => (Monoid (Set A)))
  [mempty empty])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Query
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /O(1)/. Is this the empty set?
(defn null : (∀ [A] {(Set A) -> Bool})
  [[Tip] True]
  [[(Bin _ _ _ _)] False])

;; /O(1)/. The number of elements in the set.
(defn size : (∀ [A] {(Set A) -> Integer})
  [[Tip] 0]
  [[(Bin sz _ _ _)] sz])

;; apparently hackett can't infer typeclass constraints
;; explicitly quantifying these types is a PITA

;; /O(log n)/. Is the element in the set?
(def member : (∀ [A] (Ord A) => {A -> (Set A) -> Bool})
  (letrec ([go
            (λ* [[_ Tip] False]
                [[x (Bin _ y l r)]
                 (case (compare x y)
                   [lt (go x l)]
                   [gt (go x r)]
                   [eq True])])])
    go))

;; /O(log n)/. Is the element not in the set?
(defn not-member : (∀ [A] (Ord A) => {A -> (Set A) -> Bool})
  [[a t] (not (member a t))])

;; /O(log n)/. Find largest element smaller than the given one.
;;
;; > lookupLT 3 (fromList [3, 5]) == Nothing
;; > lookupLT 5 (fromList [3, 5]) == Just 3
(def lookupLT : (∀ [A] (Ord A) => {A -> (Set A) -> (Maybe A)})
  (letrec ([go-nothing
            (λ* [[_ Tip] Nothing]
                [[x (Bin _ y l r)]
                 (if {x le? y}
                     (go-nothing x l)
                     (go-just x y r))])]
           [go-just
            (λ* [[_ best Tip] (Just best)]
                [[x best (Bin _ y l r)]
                 (if {x le? y}
                     (go-just x best l)
                     (go-just x y r))])])
    go-nothing))

;; /O(log n)/. Find smallest element greater than the given one.
;;
;; > lookupGT 4 (fromList [3, 5]) == Just 5
;; > lookupGT 5 (fromList [3, 5]) == Nothing
(def lookupGT : (∀ [A] (Ord A) => {A -> (Set A) -> (Maybe A)})
  (letrec ([go-nothing
            (λ* [[_ Tip] Nothing]
                [[x (Bin _ y l r)]
                 (if {x lt? y}
                     (go-just x y l)
                     (go-nothing x r))])]
           [go-just
            (λ* [[_ best Tip] (Just best)]
                [[x best (Bin _ y l r)]
                 (if {x lt? y}
                     (go-just x y l)
                     (go-just x best r))])])
    go-nothing))

;; | /O(log n)/. Find largest element smaller or equal to the given one.
;;
;; > lookupLE 2 (fromList [3, 5]) == Nothing
;; > lookupLE 4 (fromList [3, 5]) == Just 3
;; > lookupLE 5 (fromList [3, 5]) == Just 5
(def lookupLE : (∀ [A] (Ord A) => {A -> (Set A) -> (Maybe A)})
  (letrec ([go-nothing
            (λ* [[_ Tip] Nothing]
                [[x (Bin _ y l r)]
                 (case (compare x y)
                   [lt (go-nothing x l)]
                   [eq (Just y)]
                   [gt (go-just x y r)])])]
           [go-just
            (λ* [[_ best Tip] (Just best)]
                [[x best (Bin _ y l r)]
                 (case (compare x y)
                   [lt (go-just x best l)]
                   [eq (Just y)]
                   [gt (go-just x y r)])])])
    go-nothing))

;; | /O(log n)/. Find smallest element greater or equal to the given one.
;;
;; > lookupGE 3 (fromList [3, 5]) == Just 3
;; > lookupGE 4 (fromList [3, 5]) == Just 5
;; > lookupGE 6 (fromList [3, 5]) == Nothing
(def lookupGE : (∀ [A] (Ord A) => {A -> (Set A) -> (Maybe A)})
  (letrec ([go-nothing
            (λ* [[_ Tip] Nothing]
                [[x (Bin _ y l r)]
                 (case (compare x y)
                   [lt (go-just x y l)]
                   [eq (Just y)]
                   [gt (go-nothing x r)])])]
           [go-just
            (λ* [[_ best Tip] (Just best)]
                [[x best (Bin _ y l r)]
                 (case (compare x y)
                   [lt (go-just x y l)]
                   [eq (Just y)]
                   [gt (go-just x best r)])])])
    go-nothing))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CONSTRUCTION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; | /O(1)/. The empty set.
(def empty : (∀ [A] (Set A))
  Tip)

;; | /O(1)/. Create a singleton set.
(defn singleton : (∀ [A] {A -> (Set A)})
  [[x] (Bin 1 x Tip Tip)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Insertion, Deletion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /O(log n)/. Insert an element in a set.
;; If the set already contains an element equal to the given value,
;; it is replaced with the new value.
(defn insert : (∀ [A] (Ord A) => {A -> (Set A) -> (Set A)})
  [[x0]
   (letrec ([go : (∀ [A] (Ord A) => {A -> A -> (Set A) -> (Set A)})
             (λ* [[orig _ Tip] (singleton (lazy orig))]
                 [[orig x (Bin sz y l r)]
                  (case (compare x y)
                    [lt (let ([l2 (go orig x l)])
                          (if (ptr-eq? l2 l)
                              (Bin sz y l r) ;; this used an @ pattern originally
                              (balanceL y l2 r)))]
                    [gt (let ([r2 (go orig x r)])
                          (if (ptr-eq? r2 r)
                              (Bin sz y l r) ;; this used an @ pattern originally
                              (balanceR y l r2)))]
                    [eq
                     (Bin sz (lazy orig) l r)
                     ;; since the desired semantics of this actually relies on ptr-eq, default to
                     ;; always reconstructing the node with the original argument
                     #;(if (ptr-eq? orig y)
                            (Bin sz y l r) ;; this used an @ pattern originally
                            (Bin sz (lazy orig) l r))])])])
     (go x0 x0))])

;; I don't know what this is for.
(defn lazy
  [[x] x])

;; stand-in in case Hackett ever provides this
(defn ptr-eq? : (∀ [A] (Eq A) => {A -> A -> Bool})
  [[x y] {x == y}])

;; Insert an element to the set only if it is not in the set.
;; Used by `union`.
(defn insertR : (∀ [A] (Ord A) => {A -> (Set A) -> (Set A)})
  [[x0]
   (letrec ([go : (∀ [A] (Ord A) => {A -> A -> (Set A) -> (Set A)})
             (λ* [[orig _ Tip] (singleton (lazy orig))]
                 [[orig x t] ;; @ pattern used
                  (case t
                    [(Bin _ y l r)
                     (case (compare x y)
                       [lt (let ([ll (go orig x l)])
                             (if (ptr-eq? ll l)
                                 t
                                 (balanceL y ll r)))]
                       [gt (let ([rr (go orig x r)])
                             (if (ptr-eq? rr r)
                                 t
                                 (balanceR y l rr)))]
                       [eq t])]
                    [_ undefined!])])])
     (go x0 x0))])

;; /O(log n)/. Delete an element from a set.
(def delete : (∀ [A] (Ord A) => {A -> (Set A) -> (Set A)})
  (letrec ([go : (∀ [A] (Ord A) => {A -> (Set A) -> (Set A)})
            (λ* [[_ Tip] Tip]
                [[x (Bin s y l r)]  ;; @ pattern used
                 (case (compare x y)
                   [lt (let ([ll (go x l)])
                         (if (ptr-eq? ll l)
                             (Bin s y l r)
                             (balanceR y ll r)))]
                   [gt (let ([rr (go x r)])
                         (if (ptr-eq? rr r)
                             (Bin s y l r)
                             (balanceL y l rr)))]
                   [eq (glue l r)])])])
    go))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Subset
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /O(n+m)/. Is this a proper subset? (ie. a subset but not equal).
(defn isProperSubsetOf? : (∀ [A] (Ord A) => {(Set A) -> (Set A) -> Bool})
  [[s1 s2] {{(size s1) < (size s2)} && {s1 isSubsetOf? s2}}])

;; /O(n+m)/. Is this a subset?
;; @(s1 `isSubsetOf` s2)@ tells whether @s1@ is a subset of @s2@.
(defn isSubsetOf? : (∀ [A] (Ord A) => {(Set A) -> (Set A) -> Bool})
  [[t1 t2] {{(size t1) <= (size t2)} && {t1 isSubsetOfX? t2}}])

(defn isSubsetOfX? : (∀ [A] (Ord A) => {(Set A) -> (Set A) -> Bool})
  [[Tip _] True]
  [[_ Tip] False]
  [[(Bin _ x l r) t]
   (case (splitMember x t)
     [(Triple ls found gs)
      {found && {l isSubsetOfX? ls} && {r isSubsetOfX? gs}}])])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Disjoint
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; /O(n+m)/. Check whether two sets are disjoint (i.e. their intersection
;;   is empty).
;;
;; > disjoint (fromList [2,4,6])   (fromList [1,3])     == True
;; > disjoint (fromList [2,4,6,8]) (fromList [2,3,5,7]) == False
;; > disjoint (fromList [1,2])     (fromList [1,2,3,4]) == False
;; > disjoint (fromList [])        (fromList [])        == True
;;
(defn disjoint : (∀ [A] (Ord A) => {(Set A) -> (Set A) -> Bool})
  [[Tip _] True]
  [[_ Tip] True]
  [[(Bin _ x l r) t]
   (case (splitMember x t)
     [(Triple ls found gs)
      {(not found) && (disjoint l ls) && (disjoint r gs)}])])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Minimal, Maximal
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn lookupMinSure : (∀ [A] {A -> (Set A) -> A})
  [[x Tip] x]
  [[_ (Bin _ x l _)] (lookupMinSure x l)])

;; /O(log n)/. The minimal element of a set.
(defn lookupMin : (∀ [A] {(Set A) -> (Maybe A)})
  [[Tip] Nothing]
  [[(Bin _ x l _)] (Just (lookupMinSure x l))])

;; /O(log n)/. The minimal element of a set.
(defn findMin : (∀ [A] {(Set A) -> A})
  [[t] (case (lookupMin t)
         [(Just r) r]
         [_ (error! "Set.findMin: empty set has no minimal element")])])

(defn lookupMaxSure : (∀ [A] {A -> (Set A) -> A})
  [[x Tip] x]
  [[_ (Bin _ x _ r)] (lookupMaxSure x r)])

;; /O(log n)/. The maximal element of a set.
(defn lookupMax : (∀ [A] {(Set A) -> (Maybe A)})
  [[Tip] Nothing]
  [[(Bin _ x _ r)] (Just (lookupMaxSure x r))])

;; /O(log n)/. The maximal element of a set.
(defn findMax : (∀ [A] {(Set A) -> A})
  [[t] (case (lookupMax t)
         [(Just r) r]
         [_ (error! "Set.findMin: empty set has no minimal element")])])

;; /O(log n)/. Delete the minimal element. Returns an empty set if the set is empty.
(defn deleteMin : (∀ [A] {(Set A) -> (Set A)})
  [[(Bin _ _ Tip r)] r]
  [[(Bin _ x l r)] (balanceR x (deleteMin l) r)]
  [[Tip] Tip])

;; /O(log n)/. Delete the maximal element. Returns an empty set if the set is empty.
(defn deleteMax : (∀ [A] {(Set A) -> (Set A)})
  [[(Bin _ _ l Tip)] l]
  [[(Bin _ x l r)] (balanceL x l (deleteMax r))]
  [[Tip] Tip])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Union
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The union of a list of sets: (@'unions' == 'foldl' 'union' 'empty'@).
(def unions : (∀ [A] (Ord A) => {(List (Set A)) -> (Set A)})
  (foldl union empty))

;; /O(m*log(n\/m + 1)), m <= n/. The union of two sets, preferring the first set when
;; equal elements are encountered.
(defn union : (∀ [A] (Ord A) => {(Set A) -> (Set A) -> (Set A)})
  [[t1 Tip] t1]
  [[t1 (Bin _ x Tip Tip)] (insertR x t1)]
  [[(Bin _ x Tip Tip) t2] (insert x t2)]
  [[Tip t2] t2]
  [[(Bin s1 x l1 r1) t2] ;; @ pattern used
   (case (splitS x t2)
     [(Tuple l2 r2)
      (let ([l1l2 (union l1 l2)]
            [r1r2 (union r1 r2)])
        (if {(ptr-eq? l1l2 l1) && (ptr-eq? r1r2 r1)}
            (Bin s1 x l1 r1)
            (link x l1l2 r1r2)))])])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Difference
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; /O(m*log(n\/m + 1)), m <= n/. Difference of two sets.
(defn difference : (∀ [A] (Ord A) => {(Set A) -> (Set A) -> (Set A)})
  [[Tip _] Tip]
  [[t1 Tip] t1]
  [[t1 (Bin _ x l2 r2)]
   (case (split x t1)
     [(Tuple l1 r1)
      (let ([l1l2 (difference l1 l2)]
            [r1r2 (difference r1 r2)])
        (if {(size l1l2) + (size r1r2) == (size t1)}
            t1
            (merge l1l2 r1r2)))])])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Intersection
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /O(m*log(n\/m + 1)), m <= n/. The intersection of two sets.
;; Elements of the result come from the first set, so for example
;;
;; > import qualified Data.Set as S
;; > data AB = A | B deriving Show
;; > instance Ord AB where compare _ _ = EQ
;; > instance Eq AB where _ == _ = True
;; > main = print (S.singleton A `S.intersection` S.singleton B,
;; >               S.singleton B `S.intersection` S.singleton A)
;;
;; prints @(fromList [A],fromList [B])@.
(defn intersection : (∀ [A] (Ord A) => {(Set A) -> (Set A) -> (Set A)})
  [[Tip _] Tip]
  [[_ Tip] Tip]
  [[t1 t2] ;; @ pattern used
   (case t1
     [(Bin _ x l1 r1)
      (case (splitMember x t2)
        [(Triple l2 b r2)
         (let ([l1l2 (intersection l1 l2)]
               [r1r2 (intersection r1 r2)])
           (if b
               (if {(ptr-eq? l1l2 l1) && (ptr-eq? r1r2 r1)}
                   t1
                   (link x l1l2 r1r2))
               (merge l1l2 r1r2)))])]
     [_ (error! ":'(")])])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Filter and partition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; /O(n)/. Filter all elements that satisfy the predicate.
(defn set-filter : (∀ [A] (Eq A) => {{A -> Bool} -> (Set A) -> (Set A)})
  [[_ Tip] Tip]
  [[p (Bin s x l r)] ;; @ pattern used
   (let ([l2 (set-filter p l)]
         [r2 (set-filter p r)])
     (if (p x)
         (if {(ptr-eq? l l2) && (ptr-eq? r r2)}
             (Bin s x l r)
             (link x l2 r2))
         (merge l2 r2)))])

;; /O(n)/. Partition the set into two sets, one with all elements that satisfy
;; the predicate and one with all elements that don't satisfy the predicate.
;; See also 'split'.
(defn partition : (∀ [A] (Eq A) => {{A -> Bool} -> (Set A) -> (Tuple (Set A) (Set A))})
  [[p0 t0]
   (letrec ([go (λ* [[_ Tip] (Tuple Tip Tip)]
                    [[p (Bin s x l r)] ;; @ pattern used
                     (case* [(go p l) (go p r)]
                       [[(Tuple l1 l2) (Tuple r1 r2)]
                        (if (p x)
                            (Tuple (if {(ptr-eq? l1 l) && (ptr-eq? r1 r)}
                                       (Bin s x l r)
                                       (link x l1 r1))
                                   (merge l2 r2))
                            (Tuple (merge l1 r1)
                                   (if {(ptr-eq? l2 l) && (ptr-eq? r2 r)}
                                       (Bin s x l r)
                                       (link x l2 r2))))])])])
     (go p0 t0))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Map
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /O(n*log n)/.
;; @'map' f s@ is the set obtained by applying @f@ to each element of @s@.
;;
;; It's worth noting that the size of the result may be smaller if,
; for some @(x,y)@, @x \/= y && f x == f y@
(defn set-map : (∀ [A B] (Ord B) => {{A -> B} -> (Set A) -> (Set B)})
  [[f s] (fromList (map f (toList s)))])

;; | /O(n)/. The
;;
;; @'mapMonotonic' f s == 'map' f s@, but works only when @f@ is strictly increasing.
;; /The precondition is not checked./
;; Semi-formally, we have:
;;
;; > and [x < y ==> f x < f y | x <- ls, y <- ls]
;; >                     ==> mapMonotonic f s == map f s
;; >     where ls = toList s
(defn mapMonotonic : (∀ [A B] {{A -> B} -> (Set A) -> (Set B)})
  [[_ Tip] Tip]
  [[f (Bin sz x l r)] (Bin sz (f x) (mapMonotonic f l) (mapMonotonic f r))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fold
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /O(n)/. Fold the elements in the set using the given right-associative
;; binary operator, such that @'foldr' f z == 'Prelude.foldr' f z . 'toAscList'@.
;;
;; For example,
;;
;; > toAscList set = foldr (:) [] set
(defn set-foldr : (∀ [A B] {{A -> B -> B} -> B -> (Set A) -> B})
  [[f z]
   (letrec [(go
             (λ* [[zz Tip] zz]
                 [[zz (Bin _ x l r)] (go (f x (go zz r)) l)]))]
     (go z))])

;; /O(n)/. Fold the elements in the set using the given left-associative
;; binary operator, such that @'foldl' f z == 'Prelude.foldl' f z . 'toAscList'@.
;;
;; For example,
;;
;; > toDescList set = foldl (flip (:)) [] set
(defn set-foldl : (∀ [A B] {{A -> B -> A} -> A -> (Set B) -> A})
  [[f z]
   (letrec ([go (λ* [[z2 Tip] z2]
                    [[z2 (Bin _ x l r)] (go (f (go z2 l) x) r)])])
     (go z))])

;; currently doesn't typecheck, likely due to a bug in hackett
#;(defn foldMap : (∀ [A B] (Monoid B) => {{A -> B} -> (Set A) -> B})
  [[f t]
   (letrec ([go (λ* [[Tip] mempty]
                    [[(Bin s k l r)]
                     (if {s == 1}
                         (f k)
                         {(go l) ++ {(f k) ++ (go r)}})])])
     (go t))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /O(n)/. Convert the set to an ascending list of elements. Subject to list fusion.
(def toAscList : (∀ [A] {(Set A) -> (List A)})
  (set-foldr :: Nil))

;; /O(n)/. Convert the set to a list of elements. Subject to list fusion.
(def toList : (∀ [A] {(Set A) -> (List A)})
  toAscList)

;; /O(n*log n)/. Create a set from a list of elements.
;;
;; If the elements are ordered, a linear-time implementation is used,
;; with the performance equal to 'fromDistinctAscList'.

;; For some reason, when 'singleton' is used in fromList or in
;; create, it is not inlined, so we inline it manually.
(def fromList : (∀ [A] (Ord A) => {(List A) -> (Set A)})
  (letrec ([not-ordered? (λ* [[_ Nil] False]
                             [[x {y :: _}] {x ge? y}])]
           [fromList2 (λ [t0 xs] (foldl (flip insert) t0 xs))]
           [go (λ* [[_ t Nil] t]
                   [[_ t {x :: Nil}] (insertMax x t)]
                   [[s l {x :: xss}] ;; @ pattern used
                    (let ([xs {x :: xss}])
                      (if (not-ordered? x xss)
                          (fromList2 l xs)
                          (case (create s xss)
                            [(Triple r ys Nil) (go (shiftL s 1) (link x l r) ys)]
                            [(Triple r _ ys) (fromList2 (link x l r) ys)])))])]
           ;; The create is returning a triple (tree, xs, ys). Both xs and ys
           ;; represent not yet processed elements and only one of them can be nonempty.
           ;; If ys is nonempty, the keys in ys are not ordered with respect to tree
           ;; and must be inserted using fromList'. Otherwise the keys have been
           ;; ordered so far.
           [create (λ* [[_ Nil] (Triple Tip Nil Nil)]
                       [[s {x :: xss}] ;; @ pattern used
                        (let ([xs {x :: xss}])
                          (if {s == 1}
                              (if (not-ordered? x xss)
                                  (Triple (Bin 1 x Tip Tip) Nil xss)
                                  (Triple (Bin 1 x Tip Tip) xss Nil))
                              (case (create (shiftR s 1) xs)
                                [(Triple a Nil b) (Triple a Nil b)] ;; @ pattern used
                                [(Triple l {y :: Nil} zs) (Triple (insertMax y l) Nil zs)]
                                [(Triple l {y :: yss} _) ;; @ pattern used
                                 (let ([ys {y :: yss}])
                                   (if (not-ordered? y yss)
                                       (Triple l Nil ys)
                                       (case (create (shiftR s 1) yss)
                                         [(Triple r zs ws) (Triple (link y l r) zs ws)])))]
                                [_ (error! "See above note about invariant")])))])])
  (λ* [[Nil] Tip]
      [[{x :: Nil}] (Bin 1 x Tip Tip)]
      [[{x0 :: xs0}]
       (if (not-ordered? x0 xs0)
           (fromList2 (Bin 1 x0 Tip Tip) xs0)
           (go 1 (Bin 1 x0 Tip Tip) xs0))])))

;; /O(n)/. Convert the set to a descending list of elements. Subject to list
;; fusion.
(def toDescList : (∀ [A] {(Set A) -> (List A)})
  (set-foldl (flip ::) Nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Building trees from ascending/descending lists can be done in linear time.
;;
;;  Note that if [xs] is ascending that:
;;    fromAscList xs == fromList xs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /O(n)/. Build a set from an ascending list in linear time.
;; /The precondition (input list is ascending) is not checked./
(defn fromAscList : (∀ [A] (Eq A) => {(List A) -> (Set A)})
  [[xs] (fromDistinctAscList (combineEq xs))])

;; /O(n)/. Build a set from a descending list in linear time.
;; /The precondition (input list is descending) is not checked./
(defn fromDescList : (∀ [A] (Eq A) => {(List A) -> (Set A)})
  [[xs] (fromDistinctDescList (combineEq xs))])

;; [combineEq xs] combines equal elements with [const] in an ordered list [xs]
;;
;; TODO: combineEq allocates an intermediate list. It *should* be better to
;; make fromAscListBy and fromDescListBy the fundamental operations, and to
;; implement the rest using those.
(defn combineEq : (∀ [A] (Eq A) => {(List A) -> (List A)})
  [[Nil] Nil]
  [[{x :: xs}]
   (letrec ([combineEq2 (λ* [[z Nil] {z :: Nil}]
                            [[z {y :: ys}]
                             (if {z == y}
                                 (combineEq2 z ys)
                                 {z :: (combineEq2 y ys)})])])
     (combineEq2 x xs))])

;; | /O(n)/. Build a set from an ascending list of distinct elements in linear time.
;; /The precondition (input list is strictly ascending) is not checked./

;; For some reason, when 'singleton' is used in fromDistinctAscList or in
;; create, it is not inlined, so we inline it manually.
(defn fromDistinctAscList : (∀ [A] {(List A) -> (Set A)})
  [[Nil] Tip]
  [[{x0 :: xs0}]
   (letrec ([go (λ* [[_ t Nil] t]
                    [[s l {x :: xs}]
                     (case (create s xs)
                       [(Tuple r ys) (let ([t2 (link x l r)])
                                       (go (shiftL s 1) t2 ys))])])]
            [create (λ* [[_ Nil] (Tuple Tip Nil)]
                        [[s {x :: xs2}] ;; @ pattern used
                         (let ([xs {x :: xs2}])
                           (if {s == 1}
                               (Tuple (Bin 1 x Tip Tip) xs2)
                               (case (create (shiftR s 1) xs)
                                 [(Tuple x Nil) (Tuple x Nil)] ;; @ pattern used
                                 [(Tuple l {y :: ys})
                                  (case (create (shiftR s 1) ys)
                                    [(Tuple r zs) (Tuple (link y l r) zs)])])))])])
     (go 1 (Bin 1 x0 Tip Tip) xs0))])

;; /O(n)/. Build a set from a descending list of distinct elements in linear time.
;; /The precondition (input list is strictly descending) is not checked./

;; For some reason, when 'singleton' is used in fromDistinctDescList or in
;; create, it is not inlined, so we inline it manually.
(defn fromDistinctDescList : (∀ [A] {(List A) -> (Set A)})
  [[Nil] Tip]
  [[{x0 :: xs0}]
   (letrec ([go (λ* [[_ t Nil] t]
                    [[s r {x :: xs}]
                     (case (create s xs)
                       [(Tuple l ys) (let ([t2 (link x l r)])
                                       (go (shiftL s 1) t2 ys))])])]
            [create (λ* [[_ Nil] (Tuple Tip Nil)]
                        [[s {x :: xs2}] ;; @ pattern used
                         (let ([xs {x :: xs2}])
                           (if {s == 1}
                               (Tuple (Bin 1 x Tip Tip) xs2)
                               (case (create (shiftR s 1) xs)
                                 [(Tuple x Nil) (Tuple x Nil)] ;; @ pattern used
                                 [(Tuple r {y :: ys})
                                  (case (create (shiftR s 1) ys)
                                    [(Tuple l zs) (Tuple (link y l r) zs)])])))])])
     (go 1 (Bin 1 x0 Tip Tip) xs0))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  List variations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; /O(n)/. An alias of 'toAscList'. The elements of a set in ascending order.
;; Subject to list fusion.
(def elems : (∀ [A] {(Set A) -> (List A)})
  toAscList)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Split
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /O(log n)/. The expression (@'split' x set@) is a pair @(set1,set2)@
;; where @set1@ comprises the elements of @set@ less than @x@ and @set2@
;; comprises the elements of @set@ greater than @x@.
(defn split : (∀ [A] (Ord A) => {A -> (Set A) -> (Tuple (Set A) (Set A))})
  [[x t] (splitS x t)])

;; originally returned a `StrictPair`
(defn splitS : (∀ [A] (Ord A) => {A -> (Set A) -> (Tuple (Set A) (Set A))})
  [[_ Tip] (Tuple Tip Tip)]
  [[x (Bin _ y l r)]
   (case (compare x y)
     [lt (case (splitS x l)
           [(Tuple ls gs) (Tuple ls (link y gs r))])]
     [gt (case (splitS x r)
           [(Tuple ls gs) (Tuple (link y l ls) gs)])]
     [eq (Tuple l r)])])

(defn splitMember : (∀ [A] (Ord A) => {A -> (Set A) -> (Triple (Set A) Bool (Set A))})
  [[_ Tip] (Triple Tip False Tip)]
  [[x (Bin _ y l r)]
   (case (compare x y)
     [lt (case (splitMember x l)
           [(Triple ls found gs)
            (let ([gs2 (link y gs r)])
              (Triple ls found gs2))])]
     [gt (case (splitMember x r)
           [(Triple ls found gs)
            (let ([ls2 (link y l ls)])
              (Triple ls2 found gs))])]
     [eq (Triple l True r)])])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Indexing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /O(log n)/. Return the /index/ of an element, which is its zero-based
;; index in the sorted sequence of elements. The index is a number from /0/ up
;; to, but not including, the 'size' of the set. Calls 'error' when the element
;; is not a 'member' of the set.
;;
;; > findIndex 2 (fromList [5,3])    Error: element is not in the set
;; > findIndex 3 (fromList [5,3]) == 0
;; > findIndex 5 (fromList [5,3]) == 1
;; > findIndex 6 (fromList [5,3])    Error: element is not in the set

(def findIndex : (∀ [A] (Ord A) => {A -> (Set A) -> Integer})
  (letrec ([go : (∀ [A] (Ord A) => {Integer -> A -> (Set A) -> Integer})
            (λ* [[_ _ Tip] (error! "Set.findIndex: element is not in the set")]
                [[idx x (Bin _ kx l r)]
                 (case (compare x kx)
                   [lt (go idx x l)]
                   [gt (go {idx + (size l) + 1} x r)]
                   [eq {idx + (size l)}])])])
    (go 0)))

;; /O(log n)/. Lookup the /index/ of an element, which is its zero-based index in
;; the sorted sequence of elements. The index is a number from /0/ up to, but not
;; including, the 'size' of the set.
;;
;; > isJust   (lookupIndex 2 (fromList [5,3])) == False
;; > fromJust (lookupIndex 3 (fromList [5,3])) == 0
;; > fromJust (lookupIndex 5 (fromList [5,3])) == 1
;; > isJust   (lookupIndex 6 (fromList [5,3])) == False
(def lookupIndex : (∀ [A] (Ord A) => {A -> (Set A) -> (Maybe Integer)})
  (letrec ([go : (∀ [A] (Ord A) => {Integer -> A -> (Set A) -> (Maybe Integer)})
            (λ* [[_ _ Tip] Nothing]
                [[idx x (Bin _ kx l r)]
                 (case (compare x kx)
                   [lt (go idx x l)]
                   [gt (go {idx + (size l) + 1} x r)]
                   [eq (Just {idx + (size l)})])])])
    (go 0)))

;; /O(log n)/. Retrieve an element by its /index/, i.e. by its zero-based
;; index in the sorted sequence of elements. If the /index/ is out of range (less
;; than zero, greater or equal to 'size' of the set), 'error' is called.
;;
;; > elemAt 0 (fromList [5,3]) == 3
; > elemAt 1 (fromList [5,3]) == 5
;; > elemAt 2 (fromList [5,3])    Error: index out of range
(defn elemAt : (∀ [A] {Integer -> (Set A) -> A})
  [[_ Tip] (error! "Set.elemAt: index out of range")]
  [[i (Bin _ x l r)]
   (let ([sizeL (size l)])
     (case (compare i sizeL)
       [lt (elemAt i l)]
       [gt (elemAt {i - sizeL - 1} r)]
       [eq x]))])

;; /O(log n)/. Delete the element at /index/, i.e. by its zero-based index in
;; the sorted sequence of elements. If the /index/ is out of range (less than zero,
;; greater or equal to 'size' of the set), 'error' is called.
;;
;; > deleteAt 0    (fromList [5,3]) == singleton 5
;; > deleteAt 1    (fromList [5,3]) == singleton 3
;; > deleteAt 2    (fromList [5,3])    Error: index out of range
;; > deleteAt (-1) (fromList [5,3])    Error: index out of range
(defn deleteAt : (∀ [A] {Integer -> (Set A) -> (Set A)})
  [[i t]
   (case t
     [Tip (error! "Set.deleteAt: index out of range")]
     [(Bin _ x l r)
      (let ([sizeL (size l)])
        (case (compare i sizeL)
          [lt (balanceR x (deleteAt i l) r)]
          [gt (balanceL x l (deleteAt {i - sizeL - 1} r))]
          [eq (glue l r)]))])])

;; Take a given number of elements in order, beginning
;; with the smallest ones.
;;
;;
;; take n = 'fromDistinctAscList' . 'Prelude.take' n . 'toAscList'
(defn take : (∀ [A] {Integer -> (Set A) -> (Set A)})
  [[i m]
   (if {i > (size m)}
       m
       (if {i <= 0}
           Tip
           (letrec ([go (λ* [[i Tip] Tip]
                            [[i (Bin _ x l r)]
                             (let ([sizeL (size l)])
                               (case (compare i sizeL)
                                 [lt (go i l)]
                                 [gt (link x l (go {i - sizeL - i} r))]
                                 [eq l]))])])
             (go i m))))])

;; Drop a given number of elements in order, beginning
;; with the smallest ones.
;;
;; drop n = 'fromDistinctAscList' . 'Prelude.drop' n . 'toAscList'
(defn drop : (∀ [A] {Integer -> (Set A) -> (Set A)})
  [[i m]
   (if {i >= (size m)}
       Tip
       (letrec ([go (λ* [[_ Tip] Tip]
                        [[i (Bin s x l r)]
                         (if {i < 0}
                             (Bin s x l r)
                             (let ([sizeL (size l)])
                               (case (compare i sizeL)
                                 [lt (link x (go i l) r)]
                                 [gt (go {i - sizeL - 1} r)]
                                 [eq (insertMin x r)])))])])
         (go i m)))])

(defn splitAt : (∀ [A] {Integer -> (Set A) -> (Tuple (Set A) (Set A))})
  [[i0 m0]
   (if {i0 >= (size m0)}
       (Tuple m0 Tip)
       (letrec ([go (λ* [[_ Tip] (Tuple Tip Tip)]
                        [[i (Bin s x l r)]
                         (if {i <= 0}
                             (Tuple Tip (Bin s x l r))
                             (let ([sizeL (size l)])
                               (case (compare i sizeL)
                                 [lt (case (go i l)
                                       [(Tuple ll lr) (Tuple ll (link x lr r))])]
                                 [gt (case (go {i - sizeL - 1} r)
                                       [(Tuple rl rr) (Tuple (link x l rl) rr)])]
                                 [eq (Tuple l (insertMin x r))])))])])
         (go i0 m0)))])

;; /O(log n)/. Take while a predicate on the elements holds.
;; The user is responsible for ensuring that for all elements @j@ and @k@ in the set,
;; @j \< k ==\> p j \>= p k@. See note at 'spanAntitone'.
;;
;; @
;; takeWhileAntitone p = 'fromDistinctAscList' . 'Data.List.takeWhile' p . 'toList'
;; takeWhileAntitone p = 'set-filter' p
;; @
(defn takeWhileAntitone : (∀ [A] {{A -> Bool} -> (Set A) -> (Set A)})
  [[_ Tip] Tip]
  [[p (Bin _ x l r)]
   (if (p x)
       (link x l (takeWhileAntitone p r))
       (takeWhileAntitone p l))])

;; /O(log n)/. Drop while a predicate on the elements holds.
;; The user is responsible for ensuring that for all elements @j@ and @k@ in the set,
;; @j \< k ==\> p j \>= p k@. See note at 'spanAntitone'.
;;
;; @
;; dropWhileAntitone p = 'fromDistinctAscList' . 'Data.List.dropWhile' p . 'toList'
;; dropWhileAntitone p = 'set-filter' (not . p)
;; @
(defn dropWhileAntitone : (∀ [A] {{A -> Bool} -> (Set A) -> (Set A)})
  [[_ Tip] Tip]
  [[p (Bin _ x l r)]
   (if (p x)
       (dropWhileAntitone p r)
       (link x (dropWhileAntitone p l) r))])

;; | /O(log n)/. Divide a set at the point where a predicate on the elements stops holding.
;; The user is responsible for ensuring that for all elements @j@ and @k@ in the set,
;; @j \< k ==\> p j \>= p k@.
;;
;; @
;; spanAntitone p xs = ('takeWhileAntitone' p xs, 'dropWhileAntitone' p xs)
;; spanAntitone p xs = partition p xs
;; @
;;
;; Note: if @p@ is not actually antitone, then @spanAntitone@ will split the set
;; at some /unspecified/ point where the predicate switches from holding to not
;; holding (where the predicate is seen to hold before the first element and to fail
;; after the last element).
(defn spanAntitone : (∀ [A] {{A -> Bool} -> (Set A) -> (Tuple (Set A) (Set A))})
  [[p0 m]
   (letrec ([go (λ* [[_ Tip] (Tuple Tip Tip)]
                    [[p (Bin _ x l r)]
                     (if (p x)
                         (case (go p r)
                           [(Tuple u v) (Tuple (link x l u) v)])
                         (case (go p l)
                           [(Tuple u v) (Tuple u (link x v r))]))])])
     (go p0 m))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
  [balance x l r] balances two trees with value x.
  The sizes of the trees should balance after decreasing the
  size of one of them. (a rotation).

  [delta] is the maximal relative difference between the sizes of
          two trees, it corresponds with the [w] in Adams' paper.
  [ratio] is the ratio between an outer and inner sibling of the
          heavier subtree in an unbalanced setting. It determines
          whether a double or single rotation should be performed
          to restore balance. It is correspondes with the inverse
          of $\alpha$ in Adam's article.

  Note that according to the Adam's paper:
  - [delta] should be larger than 4.646 with a [ratio] of 2.
  - [delta] should be larger than 3.745 with a [ratio] of 1.534.

  But the Adam's paper is errorneous:
  - it can be proved that for delta=2 and delta>=5 there does
    not exist any ratio that would work
  - delta=4.5 and ratio=2 does not work

  That leaves two reasonable variants, delta=3 and delta=4,
  both with ratio=2.

  - A lower [delta] leads to a more 'perfectly' balanced tree.
  - A higher [delta] performs less rebalancing.

  In the benchmarks, delta=3 is faster on insert operations,
  and delta=4 has slightly better deletes. As the insert speedup
  is larger, we currently use delta=3.
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def delta 3)
(def ratio 2)

#|
-- The balance function is equivalent to the following:
--
--   balance :: a -> Set a -> Set a -> Set a
--   balance x l r
--     | sizeL + sizeR <= 1   = Bin sizeX x l r
--     | sizeR > delta*sizeL  = rotateL x l r
--     | sizeL > delta*sizeR  = rotateR x l r
--     | otherwise            = Bin sizeX x l r
--     where
--       sizeL = size l
--       sizeR = size r
--       sizeX = sizeL + sizeR + 1
--
--   rotateL :: a -> Set a -> Set a -> Set a
--   rotateL x l r@(Bin _ _ ly ry) | size ly < ratio*size ry = singleL x l r
--                                 | otherwise               = doubleL x l r
--   rotateR :: a -> Set a -> Set a -> Set a
--   rotateR x l@(Bin _ _ ly ry) r | size ry < ratio*size ly = singleR x l r
--                                 | otherwise               = doubleR x l r
--
--   singleL, singleR :: a -> Set a -> Set a -> Set a
--   singleL x1 t1 (Bin _ x2 t2 t3)  = bin x2 (bin x1 t1 t2) t3
--   singleR x1 (Bin _ x2 t1 t2) t3  = bin x2 t1 (bin x1 t2 t3)
--
--   doubleL, doubleR :: a -> Set a -> Set a -> Set a
--   doubleL x1 t1 (Bin _ x2 (Bin _ x3 t2 t3) t4) = bin x3 (bin x1 t1 t2) (bin x2 t3 t4)
--   doubleR x1 (Bin _ x2 t1 (Bin _ x3 t2 t3)) t4 = bin x3 (bin x2 t1 t2) (bin x1 t3 t4)
--
-- It is only written in such a way that every node is pattern-matched only once.
--
-- Only balanceL and balanceR are needed at the moment, so balance is not here anymore.
-- In case it is needed, it can be found in Data.Map.

-- Functions balanceL and balanceR are specialised versions of balance.
-- balanceL only checks whether the left subtree is too big,
-- balanceR only checks whether the right subtree is too big.
|#

;; balanceL is called when left subtree might have been inserted to or when
;; right subtree might have been deleted from.
(defn balanceL : (∀ [A] {A -> (Set A) -> (Set A) -> (Set A)})
  [[x l r]
   (case r
     [Tip
      (case l
        [Tip (Bin 1 x Tip Tip)]
        [(Bin _ _ Tip Tip) (Bin 2 x l Tip)]
        [(Bin _ lx Tip (Bin _ lrx _ _))
         (Bin 3 lrx (Bin 1 lx Tip Tip) (Bin 1 x Tip Tip))]
        [(Bin _ lx (Bin a b c d) Tip) (Bin 3 lx (Bin a b c d) (Bin 1 x Tip Tip))] ;; @ pattern
        [(Bin ls lx (Bin lls a b c) (Bin lrs lrx lrl lrr))
         (if {lrs lt? {ratio * lls}}
             (Bin {1 + ls} lx (Bin lls a b c) (Bin {1 + lrs} x (Bin lrs lrx lrl lrr) Tip))
             (Bin {1 + ls} lrx (Bin {1 + lls + (size lrl)} lx (Bin lls a b c) lrl) (Bin {1 + (size lrr)} x lrr Tip)))])]
     [(Bin rs _ _ _)
      (case l
        [Tip (Bin {1 + rs} x Tip r)]
        [(Bin ls lx ll lr)
         (if {ls gt? {delta * rs}}
             (case* [ll lr]
               [[(Bin lls _ _ _) (Bin lrs lrx lrl lrr)]
                (if {lrs lt? {ratio * lls}}
                    (Bin {1 + ls + rs} lx ll (Bin {1 + rs + lrs} x lr r))
                    (Bin {1 + ls + rs} lrx (Bin {1 + lls + (size lrl)} lx ll lrl) (Bin {1 + rs + (size lrr)} x lrr r)))]
               [[_ _] (error! "Failure in balanceL")])
             (Bin {1 + ls + rs} x l r))])])])


;; balanceR is called when right subtree might have been inserted to or when
;; left subtree might have been deleted from.
(defn balanceR : (∀ [A] {A -> (Set A) -> (Set A) -> (Set A)})
  [[x l r]
   (case l
     [Tip
      (case r
        [Tip (Bin 1 x Tip Tip)]
        [(Bin _ _ Tip Tip) (Bin 2 x Tip r)]
        [(Bin _ rx Tip (Bin a b c d)) (Bin 3 rx (Bin 1 x Tip Tip) (Bin a b c d))] ;; @ pattern used
        [(Bin _ rx (Bin _ rlx _ _) Tip) (Bin 3 rlx (Bin 1 x Tip Tip) (Bin 1 rx Tip Tip))]
        [(Bin rs rx (Bin rls rlx rll rlr) (Bin rrs a b c))
         (if {rls lt? {ratio * rrs}}
             (Bin {1 + rs} rx (Bin {1 + rls} x Tip (Bin rls rlx rll rlr)) (Bin rrs a b c))
             (Bin {1 + rs} rlx (Bin {1 + (size rll)} x Tip rll) (Bin {1 + rrs + (size rlr)} rx rlr (Bin rrs a b c))))])]
     [(Bin ls _ _ _)
      (case r
        [Tip (Bin {1 + ls} x l Tip)]
        [(Bin rs rx rl rr)
         (if {rs gt? {delta * ls}}
             (case* [rl rr]
               [[(Bin rls rlx rll rlr) (Bin rrs _ _ _)]
                (if {rls lt? {ratio * rrs}}
                    (Bin {1 + ls + rs} rx (Bin {1 + ls + rls} x l rl) rr)
                    (Bin {1 + ls + rs} rlx (Bin {1 + ls + (size rll)} x l rll) (Bin {1 + rrs + (size rlr)} rx rlr rr)))]
               [[_ _] (error! "Failure in balanceR")])
             (Bin {1 + ls + rs} x l r))])])])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  The bin constructor maintains the size of the tree
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn bin : (∀ [A] {A -> (Set A) -> (Set A) -> (Set A)})
  [[x l r] (Bin {(size l) + (size r) + 1} x l r)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
  Utility functions that maintain the balance properties of the tree.
  All constructors assume that all values in [l] < [x] and all values
  in [r] > [x], and that [l] and [r] are valid trees.

  In order of sophistication:
    [Bin sz x l r]    The type constructor.
    [bin x l r]       Maintains the correct size, assumes that both [l]
                      and [r] are balanced with respect to each other.
    [balance x l r]   Restores the balance and size.
                      Assumes that the original tree was balanced and
                      that [l] or [r] has changed by at most one element.
    [link x l r]      Restores balance and size.

  Furthermore, we can construct a new tree from two trees. Both operations
  assume that all values in [l] < all values in [r] and that [l] and [r]
  are valid:
    [glue l r]        Glues [l] and [r] together. Assumes that [l] and
                      [r] are already balanced with respect to each other.
    [merge l r]       Merges two trees and restores balance.
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  [glue l r]: glues two trees together.
;;  Assumes that [l] and [r] are already balanced with respect to each other.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn glue : (∀ [A] {(Set A) -> (Set A) -> (Set A)})
  [[Tip r] r]
  [[l Tip] l]
  [[(Bin sl xl ll lr) (Bin sr xr rl rr)] ;; @ patterns used
   (if {sl > sr}
       (case (maxViewSure xl ll lr) ;; pattern-matching `let` used originally
         [(Tuple m ll) (balanceR m ll (Bin sr xr rl rr))])
       (case (minViewSure xr rl rr)
         [(Tuple m rr) (balanceL m (Bin sl xl ll lr) rr)]))])

;; originially returned a `StrictPair`
(def minViewSure : (∀ [A] {A -> (Set A) -> (Set A) -> (Tuple A (Set A))})
  (letrec ([go (λ* [[x Tip r] (Tuple x r)]
                   [[x (Bin _ xl ll lr) r]
                    (case (go xl ll lr)
                      [(Tuple xm lll) (Tuple xm (balanceR x lll r))])])])
    go))

;; originially returned a `StrictPair`
(def maxViewSure : (∀ [A] {A -> (Set A) -> (Set A) -> (Tuple A (Set A))})
  (letrec ([go (λ* [[x l Tip] (Tuple x l)]
                   [[x l (Bin _ xr rl rr)]
                    (case (go xr rl rr)
                      [(Tuple xm rrr) (Tuple xm (balanceL x l rrr))])])])
    go))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Link
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn link : (∀ [A] {A -> (Set A) -> (Set A) -> (Set A)})
  [[x Tip r] (insertMin x r)]
  [[x l Tip] (insertMax x l)]
  [[x (Bin sizeL y ly ry) (Bin sizeR z lz rz)] ;; @ patterns used
   (if {{delta * sizeL} < sizeR}
       (balanceL z (link x (Bin sizeL y ly ry) lz) rz)
       (if {{delta * sizeR} < sizeL}
           (balanceR y ly (link x ry (Bin sizeR z lz rz)))
           (bin x (Bin sizeL y ly ry) (Bin sizeR z lz rz))))])
;; insertMin and insertMax don't perform potentially expensive comparisons.
(defn insertMax : (∀ [A] {A -> (Set A) -> (Set A)})
  [[x Tip] (singleton x)]
  [[x (Bin _ y l r)] (balanceR y l (insertMax x r))])

(defn insertMin : (∀ [A] {A -> (Set A) -> (Set A)})
  [[x Tip] (singleton x)]
  [[x (Bin _ y l r)] (balanceL y (insertMin x l) r)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  [merge l r]: merges two trees.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn merge : (∀ [A] {(Set A) -> (Set A) -> (Set A)})
  [[Tip r] r]
  [[l Tip] l]
  [[l r] ;; @ pattern used
   (case* [l r]
     [[(Bin sizeL x lx rx) (Bin sizeR y ly ry)]
      (if {{delta * sizeL} < sizeR}
          (balanceL y (merge l ly) ry)
          (if {{delta * sizeR} < sizeL}
              (balanceR x lx (merge rx r))
              (glue l r)))]
     [[_ _] (error! ":'(")])])

;; /O(log n)/. Delete and find the minimal element.
;;
;; > deleteFindMin set = (findMin set, deleteMin set)
(defn deleteFindMin : (∀ [A] {(Set A) -> (Tuple A (Set A))})
  [[t] (case (minView t)
         [(Just r) r]
         [_ (Tuple (error! "Set.deleteFindMin: can not return the minimal element of an empty set")
                   Tip)])])

;; /O(log n)/. Delete and find the maximal element.
;;
;; > deleteFindMax set = (findMax set, deleteMax set)
(defn deleteFindMax : (∀ [A] {(Set A) -> (Tuple A (Set A))})
  [[t] (case (maxView t)
         [(Just r) r]
         [_ (Tuple (error! "Set.deleteFindMax: can not return the maximal element of an empty set")
                   Tip)])])

;; /O(log n)/. Retrieves the minimal key of the set, and the set
;; stripped of that element, or 'Nothing' if passed an empty set.
(defn minView : (∀ [A] {(Set A) -> (Maybe (Tuple A (Set A)))})
  [[Tip] Nothing]
  [[(Bin _ x l r)] (Just (minViewSure x l r))])

;; /O(log n)/. Retrieves the maximal key of the set, and the set
;; stripped of that element, or 'Nothing' if passed an empty set.
(defn maxView : (∀ [A] {(Set A) -> (Maybe (Tuple A (Set A)))})
  [[Tip] Nothing]
  [[(Bin _ x l r)] (Just (maxViewSure x l r))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; /O(1)/.  Decompose a set into pieces based on the structure of the underlying
;; tree.  This function is useful for consuming a set in parallel.
;;
;; No guarantee is made as to the sizes of the pieces; an internal, but
;; deterministic process determines this.  However, it is guaranteed that the pieces
;; returned will be in ascending order (all elements in the first subset less than all
;; elements in the second, and so on).
;;
;; Examples:
;;
;; > splitRoot (fromList [1..6]) ==
;; >   [fromList [1,2,3],fromList [4],fromList [5,6]]
;;
;; > splitRoot empty == []
;;
;;  Note that the current implementation does not return more than three subsets,
;;  but you should not depend on this behaviour because it can change in the
;;  future without notice.
(defn splitRoot : (∀ [A] {(Set A) -> (List (Set A))})
  [[Tip] Nil]
  [[(Bin _ v l r)] {l :: (singleton v) :: r :: Nil}])

;; Calculate the power set of a set: the set of all its subsets.
;;
;; @
;; t `member` powerSet s == t `isSubsetOf` s
;; @
;;
;; Example:
;;
;; @
;; powerSet (fromList [1,2,3]) =
;;   fromList [[], [1], [2], [3], [1,2], [1,3], [2,3], [1,2,3]]
;; @
(defn powerSet : (∀ [A] {(Set A) -> (Set (Set A))})
  [[xs0]
   (letrec ([step (λ [x pxs] (glue (insertMin (singleton x)
                                              (mapMonotonic (insertMin x) pxs))
                                   pxs))])
     (insertMin empty (set-foldr step Tip xs0)))])

;; Calculate the Cartesian product of two sets.
;;
;; @
;; cartesianProduct xs ys = fromList $ liftA2 (,) (toList xs) (toList ys)
;; @
;;
;; Example:
;;
;; @
;; cartesianProduct (fromList [1,2]) (fromList ['a','b']) =
;;   fromList [(1,'a'), (1,'b'), (2,'a'), (2,'b')]
;; @
(defn cartesianProduct : (∀ [A B] (Ord A) (Ord B) => {(Set A) -> (Set B) -> (Set (Tuple A B))})
  [[as bs]
   (fromList {(pure Tuple) <*> (toList as) <*> (toList bs)})
   ;; currently `foldMap` doesn't typecheck so don't use this implementation
   #;(getMergeSet (foldMap (λ [a] (MergeSet (mapMonotonic (Tuple a) bs))) as))])

;; A version of Set with peculiar Semigroup and Monoid instances.
;; The result of xs <> ys will only be a valid set if the greatest
;; element of xs is strictly less than the least element of ys.
;; This is used to define cartesianProduct.
(data (MergeSet A)
      (MergeSet (Set A)))

(instance (∀ [A] (Semigroup (MergeSet A)))
  [++ (λ* [[(MergeSet xs) (MergeSet ys)] (MergeSet (merge xs ys))])])

(instance (∀ [A] (Monoid (MergeSet A)))
  [mempty (MergeSet empty)])

;; Calculate the disjoin union of two sets.
;;
;; @ disjointUnion xs ys = map Left xs `union` map Right ys @
;;
;; Example:
;;
;; @
;; disjointUnion (fromList [1,2]) (fromList ["hi", "bye"]) =
;;   fromList [Left 1, Left 2, Right "hi", Right "bye"]
;; @
(defn disjointUnion : (∀ [A B] {(Set A) -> (Set B) -> (Set (Either A B))})
  [[as bs]
   (merge (mapMonotonic Left as) (mapMonotonic Right bs))])

#|
{--------------------------------------------------------------------
  Debugging
--------------------------------------------------------------------}
-- | /O(n)/. Show the tree that implements the set. The tree is shown
-- in a compressed, hanging format.
showTree :: Show a => Set a -> String
showTree s
  = showTreeWith True False s


{- | /O(n)/. The expression (@showTreeWith hang wide map@) shows
 the tree that implements the set. If @hang@ is
 @True@, a /hanging/ tree is shown otherwise a rotated tree is shown. If
 @wide@ is 'True', an extra wide version is shown.

> Set> putStrLn $ showTreeWith True False $ fromDistinctAscList [1..5]
> 4
> +--2
> |  +--1
> |  +--3
> +--5
>
> Set> putStrLn $ showTreeWith True True $ fromDistinctAscList [1..5]
> 4
> |
> +--2
> |  |
> |  +--1
> |  |
> |  +--3
> |
> +--5
>
> Set> putStrLn $ showTreeWith False True $ fromDistinctAscList [1..5]
> +--5
> |
> 4
> |
> |  +--3
> |  |
> +--2
>    |
>    +--1

-}
showTreeWith :: Show a => Bool -> Bool -> Set a -> String
showTreeWith hang wide t
  | hang      = (showsTreeHang wide [] t) ""
  | otherwise = (showsTree wide [] [] t) ""

showsTree :: Show a => Bool -> [String] -> [String] -> Set a -> ShowS
showsTree wide lbars rbars t
  = case t of
      Tip -> showsBars lbars . showString "|\n"
      Bin _ x Tip Tip
          -> showsBars lbars . shows x . showString "\n"
      Bin _ x l r
          -> showsTree wide (withBar rbars) (withEmpty rbars) r .
             showWide wide rbars .
             showsBars lbars . shows x . showString "\n" .
             showWide wide lbars .
             showsTree wide (withEmpty lbars) (withBar lbars) l

showsTreeHang :: Show a => Bool -> [String] -> Set a -> ShowS
showsTreeHang wide bars t
  = case t of
      Tip -> showsBars bars . showString "|\n"
      Bin _ x Tip Tip
          -> showsBars bars . shows x . showString "\n"
      Bin _ x l r
          -> showsBars bars . shows x . showString "\n" .
             showWide wide bars .
             showsTreeHang wide (withBar bars) l .
             showWide wide bars .
             showsTreeHang wide (withEmpty bars) r

showWide :: Bool -> [String] -> String -> String
showWide wide bars
  | wide      = showString (concat (reverse bars)) . showString "|\n"
  | otherwise = id

showsBars :: [String] -> ShowS
showsBars bars
  = case bars of
      [] -> id
      _  -> showString (concat (reverse (tail bars))) . showString node

|#

;; /O(n)/. Show the tree that implements the set. The tree is shown
;; in a compressed, hanging format.
(defn showTree : (∀ [A] (Show A) => {(Set A) -> String})
  [[s] (showTreeWith True False s)])

(defn showTreeWith : (∀ [A] (Show A) => {Bool -> Bool -> (Set A) -> String})
  [[hang wide t]
   (if hang
       (showsTreeHang wide Nil t)
       (showsTree wide Nil Nil t))])

(defn showsTree : (∀ [A] (Show A) => {Bool -> (List String) -> (List String) -> (Set A) -> String})
  [[wide lbars rbars t]
   (case t
     [Tip {(showBars lbars) ++ "|\n"}]
     [(Bin _ x Tip Tip)
      {(showBars lbars) ++ (show x) ++ "\n"}]
     [(Bin _ x l r)
      {(showsTree wide (withBar rbars) (withEmpty rbars) r)
       ++ (showWide wide rbars)
       ++ (showBars lbars) ++ (show x) ++ "\n"
       ++ (showWide wide lbars)
       ++ (showsTree wide (withEmpty lbars) (withBar lbars) l)}])])
                                                            

(defn showsTreeHang : (∀ [A] (Show A) => {Bool -> (List String) -> (Set A) -> String})
  [[wide bars t]
   (case t
     [Tip {(showBars bars) ++ "|\n"}]
     [(Bin _ x Tip Tip) {(showBars bars) ++ (show x) ++ "\n"}]
     [(Bin _ x l r)
      {(showBars bars) ++ (show x) ++ "\n"
                       ++ (showWide wide bars)
                       ++ (showsTreeHang wide (withBar bars) l)
                       ++ (showWide wide bars)
                       ++ (showsTreeHang wide (withEmpty bars) r)}])])

(defn showWide : {Bool -> (List String) -> String}
  [[wide bars]
   (if wide
       {(concat (reverse bars)) ++ "|\n"}
       "")])

(defn showBars : {(List String) -> String}
  [[Nil] ""]
  [[bars] {(concat (reverse (tail! bars))) ++ node}])

(def node : String
  "+--")

(defn withBar : {(List String) -> (List String)}
  [[bars] {"| " :: bars}])
(defn withEmpty : {(List String) -> (List String)}
  [[bars] {"  " :: bars}])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Assertions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /O(n)/. Test if the internal set structure is valid.
(defn valid : (∀ [A] (Ord A) => {(Set A) -> Bool})
  [[t] {(balanced t) && (ordered t) && (validsize t)}])

(defn ordered : (∀ [A] (Ord A) => {(Set A) -> Bool})
  [[t]
   (letrec ([bounded (λ* [[lo hi t2]
                          (case t2
                            [Tip True]
                            [(Bin _ x l r) {(lo x)
                                            && (hi x)
                                            && (bounded lo (λ [y] (lt? y x)) l)
                                            && (bounded (λ [y] (gt? y x)) hi r)}])])])
     (bounded (const True) (const True) t))])

(defn balanced : (∀ [A] {(Set A) -> Bool})
  [[Tip] True]
  [[(Bin _ _ l r)]
    {{{(size l) + (size r) <= 1} || {{(size l) <= {delta * (size r)}} && {(size r) <= {delta * (size l)}}}}
     && (balanced l) && (balanced r)}])

(def validsize : (∀ [A] {(Set A) -> Bool})
  (letrec ([realsize (λ* [[Tip] (Just 0)]
                         [[(Bin sz _ l r)]
                          (case (Tuple (realsize l) (realsize r))
                            [(Tuple (Just n) (Just m))
                             (if {sz == {n + m + 1}}
                                 (Just sz)
                                 Nothing)]
                            [_ Nothing])])])
    (λ [t] {(realsize t) == (Just (size t))})))