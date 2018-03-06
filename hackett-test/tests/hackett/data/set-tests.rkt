#lang hackett

(require hackett/data/set)
(require hackett/data/ord)
(require hackett/data/identity)
(require hackett/test/quickcheck)
(require hackett/monad/trans)
(require hackett/monad/state)

(require hackett/private/test)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn length : (∀ [A] {(List A) -> Integer})
  [[Nil] 0]
  [[{_ :: xs}] {1 + (length xs)}])

(defn elem : (∀ [A] (Eq A) => {A -> (List A) -> Bool})
  [[_ Nil] False]
  [[x {y :: ys}] (if {x == y}
                     True
                     (elem x ys))])

(defn notElem? : (∀ [A] (Eq A) => {A -> (List A) -> Bool})
  [[x ys] (not (elem x ys))])

(defn all : (∀ [A] {{A -> Bool} -> (List A) -> Bool})
  [[_ Nil] True]
  [[p {x :: xs}] {(p x) && (all p xs)}])

(defn any : (∀ [A] {{A -> Bool} -> (List A) -> Bool})
  [[_ Nil] False]
  [[p {x :: xs}] {(p x) || (any p xs)}])

(defn fromUpToBy : {Integer -> Integer -> Integer -> (List Integer)}
  [[base ceil step]
   (if {base > ceil}
       Nil
       {base :: (fromUpToBy {base + step} ceil step)})])

(defn fromDownToBy : {Integer -> Integer -> Integer -> (List Integer)}
  [[base floor step]
   (if {base < floor}
       Nil
       {base :: (fromDownToBy {base - step} floor step)})])

(defn sort : (∀ [A] (Ord A) => {(List A) -> (List A)})
  [[Nil] Nil]
  [[{x :: xs}]
    (let ([before (filter (λ [y] (le? y x)) xs)]
          [after (filter (λ [y] (gt? y x)) xs)])
      {(sort before) ++ {x :: (sort after)}})])

(def nub : (∀ [A] (Eq A) => {(List A) -> (List A)})
  (letrec ([insertUnique
            (λ* [[x Nil] {x :: Nil}]
                [[x {y :: ys}]
                 (if {x == y}
                     {y :: ys}
                     {y :: (insertUnique x ys)})])]
           [nubp
            (λ* [[Nil xs] xs]
                [[{x :: xs} ys]
                 (nubp xs (insertUnique x ys))])])
    (λ [xs] (nubp xs Nil))))

(defn set-all : (∀ [a] {{a -> Bool} -> (Set a) -> Bool})
  [[p s] (set-foldr (λ [x acc] {acc && (p x)}) True s)])

(defn last! : (∀ [a] {(List a) -> a})
  [[{x :: Nil}] x]
  [[{x :: xs}] (last! xs)]
  [[Nil] (error! "last! given empty list")])

;; The 'group' function takes a list and returns a list of lists such
;; that the concatenation of the result is equal to the argument.  Moreover,
;; each sublist in the result contains only equal elements.  For example,
;;
;; > group "Mississippi" = ["M","i","ss","i","ss","i","pp","i"]
;;
;; It is a special case of 'groupBy', which allows the programmer to supply
;; their own equality test.
(def group : (∀ [A] (Eq A) => {(List A) -> (List (List A))})
  (groupBy ==))


;; The 'groupBy' function is the non-overloaded version of 'group'.
(defn groupBy : (∀ [a] {{a -> a -> Bool} -> (List a) -> (List (List a))})
  [[_ Nil] Nil]
  [[p {x :: xs}]
   (case (span (p x) xs)
     [(Tuple ys zs)
      {{x :: ys} :: (groupBy p zs)}])])

;; 'span', applied to a predicate @p@ and a list @xs@, returns a tuple where
;; first element is longest prefix (possibly empty) of @xs@ of elements that
;; satisfy @p@ and second element is the remainder of the list:
;;
;; > span (< 3) [1,2,3,4,1,2,3,4] == ([1,2],[3,4,1,2,3,4])
;; > span (< 9) [1,2,3] == ([1,2,3],[])
;; > span (< 0) [1,2,3] == ([],[1,2,3])
;;
;; 'span' @p xs@ is equivalent to @('takeWhile' p xs, 'dropWhile' p xs)@
(defn span : (∀ [a] {{a -> Bool} -> (List a) -> (Tuple (List a) (List a))})
  [[_ Nil] (Tuple Nil Nil)]
  [[p {x :: xsp}] ;; @ pattern used
   (if (p x)
       (case (span p xsp)
         [(Tuple ys zs) (Tuple {x :: ys} zs)])
       (Tuple Nil {x :: xsp}))])

;; The 'deleteBy' function behaves like 'delete', but takes a
;; user-supplied equality predicate.
;;
;; >>> deleteBy (<=) 4 [1..10]
;; [1,2,3,5,6,7,8,9,10]
(defn List.deleteBy : (∀ [a] {{a -> a -> Bool} -> a -> (List a) -> (List a)})
  [[_ _ Nil] Nil]
  [[p x {y :: ys}]
   (if (p x y)
       ys
       {y :: (List.deleteBy p x ys)})])

;; 'delete' @x@ removes the first occurrence of @x@ from its list argument.
;; For example,
;;
;; >>> delete 'a' "banana"
;; "bnana"
;;
;; It is a special case of 'deleteBy', which allows the programmer to
;; supply their own equality test.
(def List.delete : (∀ [a] (Eq a) => {a -> (List a) -> (List a)})
  (List.deleteBy ==))

;; The '\\' function is list difference (non-associative).
;; In the result of @xs@ '\\' @ys@, the first occurrence of each element of
;; @ys@ in turn (if any) has been removed from @xs@.  Thus
;;
;; > (xs ++ ys) \\ xs == ys.
;;
;; >>> "Hello World!" \\ "ell W"
;; "Hoorld!"
;;
;; It is a special case of 'deleteFirstsBy', which allows the programmer
;; to supply their own equality test.
(def \\ : (∀ [a] (Eq a) => {(List a) -> (List a) -> (List a)})
  (foldl (flip List.delete)))

;; The 'intersectBy' function is the non-overloaded version of 'intersect'.
(defn List.intersectBy : (∀ [a] {{a -> a -> Bool} -> (List a) -> (List a) -> (List a)})
  [[_ Nil _] Nil]
  [[_ _ Nil] Nil]
  [[p xs ys]
   (filter (λ [x] (any (p x) ys)) xs)])

;; | The 'intersect' function takes the list intersection of two lists.
;; For example,
;;
;; >>> [1,2,3,4] `intersect` [2,4,6,8]
;; [2,4]
;;
;; If the first list contains duplicates, so will the result.
;;
;; >>> [1,2,2,3,4] `intersect` [6,4,4,2]
;; [2,2,4]
;;
;; It is a special case of 'intersectBy', which allows the programmer to
;; supply their own equality test. If the element is found in both the first
;; and the second list, the element from the first list will be used.
(def List.intersect : (∀ [a] (Eq a) => {(List a) -> (List a) -> (List a)})
  (List.intersectBy ==))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A type with a peculiar Eq instance designed to make sure keys
;; come from where they're supposed to.

(data (OddEq A)
      (OddEq A Bool))

(instance (∀ [A] (Show A) => (Show (OddEq A)))
  [show (λ* [[(OddEq a b)] {"OddEq " ++ (show a) ++ " " ++ (show b)}])])

(defn getOddEq : (∀ [A] {(OddEq A) -> (Tuple A Bool)})
  [[(OddEq a b)] (Tuple a b)])

(instance (∀ [A] (Arbitrary A) => (Arbitrary (OddEq A)))
  [arbitrary {OddEq <$> arbitrary <*> arbitrary}])

(instance (∀ [A] (Eq A) => (Eq (OddEq A)))
  [== (λ* [[(OddEq x _) (OddEq y _)] {x == y}])])

(instance (∀ [A] (Ord A) => (Ord (OddEq A)))
  [compare (λ* [[(OddEq x _) (OddEq y _)] (compare x y)])])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unit tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; test_lookupLT
(test {(lookupLT 3 (fromList {3 :: 5 :: Nil})) ==! Nothing})
(test {(lookupLT 5 (fromList {3 :: 5 :: Nil})) ==! (Just 3)})

;; test_lookupGT
(test {(lookupGT 4 (fromList {3 :: 5 :: Nil})) ==! (Just 5)})
(test {(lookupGT 5 (fromList {3 :: 5 :: Nil})) ==! Nothing})

;; test_lookupLE
(test {(lookupLE 2 (fromList {3 :: 5 :: Nil})) ==! Nothing})
(test {(lookupLE 4 (fromList {3 :: 5 :: Nil})) ==! (Just 3)})
(test {(lookupLE 5 (fromList {3 :: 5 :: Nil})) ==! (Just 5)})

;; test_lookupGE
(test {(lookupGE 3 (fromList {3 :: 5 :: Nil})) ==! (Just 3)})
(test {(lookupGE 4 (fromList {3 :: 5 :: Nil})) ==! (Just 5)})
(test {(lookupGE 6 (fromList {3 :: 5 :: Nil})) ==! Nothing})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Indexed
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn isJust
  [[(Just _)] True]
  [[Nothing] False])

(defn fromJust
  [[(Just x)] x]
  [[_] (error! "fromJust")])

;; test_lookupIndex
(test {(isJust (lookupIndex 2 (fromList {5 :: 3 :: Nil}))) ==! False})
(test {(fromJust (lookupIndex 3 (fromList {5 :: 3 :: Nil}))) ==! 0})
(test {(fromJust (lookupIndex 5 (fromList {5 :: 3 :: Nil}))) ==! 1})
(test {(isJust (lookupIndex 6 (fromList {5 :: 3 :: Nil}))) ==! False})

;; test_findIndex
(test {(findIndex 3 (fromList {5 :: 3 :: Nil})) ==! 0})
(test {(findIndex 5 (fromList {5 :: 3 :: Nil})) ==! 1})

;; test_elemAt
(test {(elemAt 0 (fromList {5 :: 3 :: Nil})) ==! 3})
(test {(elemAt 1 (fromList {5 :: 3 :: Nil})) ==! 5})

;; test_deleteAt
(test {(deleteAt 0 (fromList {5 :: 3 :: Nil})) ==! (singleton 5)})
(test {(deleteAt 1 (fromList {5 :: 3 :: Nil})) ==! (singleton 3)})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Arbitrary, reasonably balanced trees
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The IsInt class lets us constrain a type variable to be Int in an entirely
;; standard way. The constraint @ IsInt a @ is essentially equivalent to the
;; GHC-only constraint @ a ~ Int @, but @ IsInt @ requires manual intervention
;; to use. If ~ is ever standardized, we should certainly use it instead.
;; Earlier versions used an Enum constraint, but this is confusing because
;; not all Enum instances will work properly for the Arbitrary instance here.

(class (Show A) (Arbitrary A) => (IsInt A)
  [fromIntF : (∀ [F] {(F Integer) -> (F A)})])

(instance (IsInt Integer)
  [fromIntF id])

(def fromInt : (∀ [A] (IsInt A) => {Integer -> A})
  {run-identity . fromIntF . Identity})

(data (F G A B)
      (F {(G B) -> A}))
(defn unf
  [[(F f)] f])

(def toIntF : (∀ [G A] (IsInt A) => {(G A) -> (G Integer)})
  {unf . fromIntF . F $ id})


;; How much the minimum value of an arbitrary set should vary
(def positionFactor : Integer
  1)

;; How much the gap between consecutive elements in an arbitrary
;; set should vary
(def gapRange : Integer
  5)

(instance (∀ [A] (IsInt A) => (Arbitrary (Set A)))
  [arbitrary
   (let ([step (do [i <- get]
                 [diff <- (lift (choose (Tuple 1 gapRange)))]
                 (let [ip {i + diff}])
                 (put ip)
                 (pure ip))])
     (sized (λ [sz0]
              (do [sz <- (choose (Tuple 0 sz0))]
                [middle <- (choose (Tuple {(- 0 positionFactor) * {sz + 1}} {positionFactor * {sz + 1}}))]
                [t <- (let ([shift {{sz * gapRange + 1} quotient! 2}]
                            [start {middle - shift}])
                        (evalStateT (mkArb step sz) start))]
                (if (valid t)
                    (pure (fromIntF t))
                    (error! "Test generated invalid tree!"))))))]
  [shrink
   {fromIntF . fromList . toIntF . shrink . toList}])

(class (Monad m) => (MonadGen m)
  [liftGen : (∀ [a] {(Gen a) -> (m a)})])

(instance (MonadGen Gen)
  [liftGen id])

(instance (∀ [m s] (MonadGen m) => (MonadGen (StateT s m)))
  [liftGen {lift . liftGen}])

;; Given an action that produces successively larger elements and
;; a size, produce a set of arbitrary shape with exactly that size.
(defn mkArb : (∀ [m a] (MonadGen m) => {(m a) -> Integer -> (m (Set a))})
  [[step n]
   (if {n <= 0}
       (pure Tip)
       (if {n == 1}
           {singleton <$> step}
           (if {n == 2}
               (do [dir <- (liftGen arbitrary)]
                 [p <- step]
                 [q <- step]
                 (if dir
                     (pure (Bin 2 q (singleton p) Tip))
                     (pure (Bin 2 p Tip (singleton q)))))
               (let ([upper {{3 * {n - 1}} quotient! 4}]
                     ;; this assumes a balnce factor of delta = 3
                     [lower {{n + 2} quotient! 4}])
                 (do [ln <- (liftGen (choose (Tuple lower upper)))]
                   (let [rn {n - ln - 1}])
                   {(λ [l x r] (Bin n x l r))
                    <$> (mkArb step ln)
                    <*> step
                    <*> (mkArb step rn)})))))])

;; Given a strictly increasing list of elements, produce an arbitrarily
;; shaped set with exactly those elements.
(defn setFromList : (∀ [A] {(List A) -> (Gen (Set A))})
  [[xs]
   (let ([step (do [xxs <- get]
                 (case xxs
                   [{x :: xs}
                    (do (put xs)
                      (pure x))]
                   [_ (error! "setFromList case not covered")]))])
     (evalStateT (mkArb step (length xs)) xs))])

(data TwoSets
      (TwoSets (Set Integer) (Set Integer)))

(instance (Show TwoSets)
  [show (λ* [[(TwoSets t1 t2)]
             {"TwoSets " ++ (show t1) ++ " " ++ (show t2)}])])

(data (TwoLists A)
      (TwoLists (List A) (List A)))

(instance (Functor TwoLists)
  [map (λ* [[f (TwoLists l1 l2)]
            (TwoLists (map f l1) (map f l2))])])

(data Options2
      One2
      Two2
      Both2) ;; deriving (Bounded, Enum)

(instance (Arbitrary Options2)
  [arbitrary (elements {One2 :: Two2 :: Both2 :: Nil})])

;; We produce two lists from a simple "universe". This instance
;; is intended to give good results when the two lists are then
;; combined with each other; if other elements are used with them,
;; they may or may not behave particularly well.
(instance (∀ [A] (IsInt A) => (Arbitrary (TwoLists A)))
  [arbitrary (sized (λ [sz0] (do [sz <- (choose (Tuple 0 sz0))]
                               (let [universe (fromUpToBy 0 {3 * {sz - 1}} 3)])
                               (divide2Gen (fromIntF universe)))))])

(instance (Arbitrary TwoSets)
  [arbitrary (do [tl <- arbitrary]
               (case tl
                 [(TwoLists l r)
                  {TwoSets <$> (setFromList l) <*> (setFromList r)}]))])

(defn divide2Gen : (∀ [A] {(List A) -> (Gen (TwoLists A))})
  [[Nil] (pure (TwoLists Nil Nil))]
  [[{x :: xs}]
   (do [way <- arbitrary]
     [tl <- (divide2Gen xs)]
     (case tl
       [(TwoLists ls rs)
        (case way
          [One2 (pure (TwoLists {x :: ls} rs))]
          [Two2 (pure (TwoLists ls {x :: rs}))]
          [Both2 (pure (TwoLists {x :: ls} {x :: rs}))])]))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Valid trees
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn forValid : (∀ [A B] (IsInt A) (Testable B) => {{(Set A) -> B} -> Property})
  [[f]
   (forAll arbitrary
     (λ [t]
       (classify {(size t) == 0} "empty"
                 (classify {{(size t) > 0} && {(size t) <= 10}} "small"
                           (classify {{(size t) > 10} && {(size t) <= 64}} "medium"
                                     (classify {(size t) > 64} "large"
                                               (f t)))))))])

(defn forValidUnitTree : (∀ [A] (Testable A) => {{(Set Integer) -> A} -> Property})
  [[f] (forValid f)])

(def prop_Valid : Property
  (forValidUnitTree valid))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Single, Member, Insert, Delete
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn prop_Single : {Integer -> Bool}
  [[x] {(insert x empty) == (singleton x)}])

(defn prop_Member : {(List Integer) -> Integer -> Bool}
  [[xs n]
   (let ([m (fromList xs)])
     (all (λ [k] {(member k m) == (elem k xs)}) {n :: xs}))])

(defn prop_NotMember : {(List Integer) -> Integer -> Bool}
  [[xs n]
   (let ([m (fromList xs)])
     (all (λ [k] {(not-member k m) == (notElem? k xs)}) {n :: xs}))])

(defn test_LookupSomething : {{Integer -> (Set Integer) -> (Maybe Integer)}
                              -> {Integer -> Integer -> Bool}
                              -> (List Integer)
                              -> Bool}
  [[lookupp cmp xs]
   (letrec ([filter_odd
             (λ* [[Nil] Nil]
                 [[{_ :: Nil}] Nil]
                 [[{_ :: o :: xs}] {o :: (filter_odd xs)}])])
     (let ([odd_sorted_xs (filter_odd (nub (sort xs)))]
           [t (fromList odd_sorted_xs)]
           [test : {Integer -> Bool}
            (λ [x] (case (filter (λ [y] (cmp y x)) odd_sorted_xs)
                     [Nil {(lookupp x t) == Nothing}]
                     [cs
                      (if (cmp 0 1)
                          {(lookupp x t) == (Just (last! cs))} ;; we want largest such element
                          {(lookupp x t) == (Just (head! cs))})]))]) ;; we want smallest such element
       (all test xs)))])

(def prop_LookupLT : {(List Integer) -> Bool}
  (test_LookupSomething lookupLT <))

(def prop_LookupGT : {(List Integer) -> Bool}
  (test_LookupSomething lookupGT >))

(def prop_LookupLE : {(List Integer) -> Bool}
  (test_LookupSomething lookupLE <=))

(def prop_LookupGE : {(List Integer) -> Bool}
  (test_LookupSomething lookupGE >=))

(defn prop_InsertValid : {Integer -> Property}
  [[k] (forValidUnitTree (λ [t] (valid (insert k t))))])

(defn prop_InsertDelete : {Integer -> (Set Integer) -> Property}
  [[k t] {(not (member k t)) ==> {(delete k (insert k t)) == t}}])

(defn prop_InsertBiased : {Integer -> (Set Integer) -> Bool}
  [[k t]
   (let ([tp (mapMonotonic (λ [x] (OddEq x False)) t)]
         [ktp (insert (OddEq k True) tp)]
         [kt (mapMonotonic getOddEq ktp)])
     (member (Tuple k True) kt))])

(defn prop_DeleteValid : {Integer -> Property}
  [[k] (forValidUnitTree (λ [t] (valid (delete k (insert k t)))))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Balance
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn prop_Link : {Integer -> Property}
  [[x]
   (forValidUnitTree (λ [t]
                       (case (split x t)
                         [(Tuple l r) (valid (link x l r))])))])

(defn prop_Merge : {Integer -> Property}
  [[x]
   (forValidUnitTree (λ [t]
                       (case (split x t)
                         [(Tuple l r) (valid (merge l r))])))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Union
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def prop_UnionValid : Property
  (forValidUnitTree
      (λ [t1]
        (forValidUnitTree
            (λ [t2]
              (valid (union t1 t2)))))))

(defn prop_UnionInsert : {Integer -> (Set Integer) -> Bool}
  [[x t] {(union t (singleton x)) == (insert x t)}])

(defn prop_UnionAssoc : {(Set Integer) -> (Set Integer) -> (Set Integer) -> Bool}
  [[t1 t2 t3] {(union t1 (union t2 t3)) == (union (union t1 t2) t3)}])

(defn prop_UnionComm : {TwoSets -> Bool}
  [[(TwoSets t1 t2)] {(union t1 t2) == (union t2 t1)}])

(defn prop_UnionBiased : {TwoSets -> Bool}
  [[(TwoSets l r)]
   (let ([lp (mapMonotonic (λ [x] (OddEq x False)) l)]
         [rp (mapMonotonic (λ [x] (OddEq x True)) l)])
     {(union lp rp) == (union lp (difference rp lp))})])

(defn prop_IntBiased : {TwoSets -> Bool}
  [[(TwoSets l r)]
   (let ([lp (mapMonotonic (λ [x] (OddEq x False)) l)]
         [rp (mapMonotonic (λ [x] (OddEq x True)) l)]
         [lprp (intersection lp rp)])
     (set-all (λ* [[(OddEq _ b)] (not b)]) lprp))])

(def prop_DiffValid : Property
  (forValidUnitTree(λ [t1] (forValidUnitTree (λ [t2] (valid (difference t1 t2)))))))

(defn prop_Diff : {(List Integer) -> (List Integer) -> Bool}
  [[xs ys]
   {(toAscList (difference (fromList xs) (fromList ys)))
    == (sort (\\ (nub xs) (nub ys)))}])

(def prop_IntValid : Property
  (forValidUnitTree (λ [t1] (forValidUnitTree (λ [t2] (valid (intersection t1 t2)))))))

(defn prop_Int : {(List Integer) -> (List Integer) -> Bool}
  [[xs ys]
   {(toAscList (intersection (fromList xs) (fromList ys)))
    == (sort (nub (List.intersect xs ys)))}])

(defn prop_disjoint : {(Set Integer) -> (Set Integer) -> Bool}
  [[a b] {(disjoint a b) == (null (intersection a b))}])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def prop_Ordered : Property
  (forAll (choose (Tuple 5 100))
    (λ [n] (let ([xs (fromUpToBy 0 n 1)])
             ;; the haskell source uses `===` but I don't know what that is
             {(fromAscList xs) == (fromList xs)}))))

(def prop_DescendingOrdered : Property
  (forAll (choose (Tuple 5 100))
    (λ [n] (let ([xs (fromDownToBy n 0 1)])
             ;; the haskell source uses `===` but I don't know what that is
             {(fromDescList xs) == (fromList xs)}))))

(defn prop_List : {(List Integer) -> Bool}
  [[xs] {(sort (nub xs)) == (toList (fromList xs))}])

(defn prop_DescList : {(List Integer) -> Bool}
  [[xs] {(reverse (sort (nub xs))) == (toDescList (fromList xs))}])

(defn prop_AscDescList : {(List Integer) -> Bool}
  [[xs] (let ([s (fromList xs)])
          {(toAscList s) == (reverse (toDescList s))})])

(defn prop_fromList : {(List Integer) -> Bool}
  [[xs]
   (let ([t (fromList xs)]
         [sort_xs (sort xs)]
         [nub_sort_xs (map head! (group sort_xs))])
     {{t == (fromAscList sort_xs)}
      && {t == (fromDistinctAscList nub_sort_xs)}
      && {t == (foldr insert empty xs)}})])

(defn prop_fromListDesc : {(List Integer) -> Bool}
  [[xs]
   (let ([t (fromList xs)]
         [sort_xs (reverse (sort xs))]
         [nub_sort_xs (map head! (group sort_xs))])
     {{t == (fromDescList sort_xs)}
      && {t == (fromDistinctDescList nub_sort_xs)}
      && {t == (foldr insert empty xs)}})])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Set operations are like IntSet operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ... a bunch of tests making use of IntSet which doesn't exist for us ...

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Main
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(main (do (quickCheck prop_Valid)
        (quickCheck prop_Single)
        (quickCheck prop_Member)
        (quickCheck prop_NotMember)
        (quickCheck prop_InsertValid)
        (quickCheck prop_InsertDelete)
        ;; prop_InsertBiased is failing
        (quickCheck prop_InsertBiased)
        (quickCheck prop_DeleteValid)
        (quickCheck prop_Link)
        (quickCheck prop_Merge)
        (quickCheck prop_UnionValid)
        (quickCheck prop_UnionInsert)
        (quickCheck prop_UnionAssoc)
        (quickCheck prop_DiffValid)
        (quickCheck prop_IntValid)
        (quickCheck prop_disjoint)
        (quickCheck prop_Ordered)
        (quickCheck prop_DescendingOrdered)
        (quickCheck prop_List)
        (quickCheck prop_DescList)
        (quickCheck prop_AscDescList)
        (quickCheck prop_UnionComm)
        (quickCheck prop_UnionBiased)
        (quickCheck prop_IntBiased)
        (quickCheck prop_LookupLT)
        (quickCheck prop_LookupGT)
        (quickCheck prop_LookupLE)
        (quickCheck prop_LookupGE)
        (quickCheck prop_fromList)
        (quickCheck prop_fromListDesc)
        (quickCheck prop_Diff)
        (quickCheck prop_Int)))

#|
(def k 1)
 (def t (fromList {1 :: 3 ::  Nil}))
(def tp (mapMonotonic (λ [x] (OddEq x False)) t))
(def ktp (insert (OddEq k True) tp))
(def kt (mapMonotonic getOddEq ktp))
|#