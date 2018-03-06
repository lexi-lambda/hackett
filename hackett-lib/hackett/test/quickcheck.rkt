#lang hackett

;; minimal quickcheck implementation following Claessen, Hughes ICFP'00
;; http://www.eecs.northwestern.edu/~robby/courses/395-495-2009-fall/quick.pdf

(require hackett/system/random)

(provide Gen
         (class Arbitrary)
         (class Coarbitrary)
         (class Testable)
         choose
         variant
         promote
         sized
         elements
         vector
         oneof
         frequency
         Result
         ok
         stamp
         arguments
         nothing
         result
         (data Property)
         evaluate
         forAll
         ==>
         label
         classify
         collect
         quickCheck
         generate)
         

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utilties
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn !! : (∀ [A] {(List A) -> Integer -> A})
  [[{x :: xs} n]
   (if {n == 0}
       x
       {xs !! {n - 1}})]
  [[_ _] (error! "!! index out of range")])

(defn length : (∀ [A] {(List A) -> Integer})
  [[Nil] 0]
  [[{_ :: xs}] {1 + (length xs)}])

(defn repeat : (∀ [A] {Integer -> A -> (List A)})
  [[n x]
   (if {n == 0}
       Nil
       {x :: (repeat {n - 1} x)})])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(data (Gen A)
      (Gen {Integer -> StdGen -> A}))

(defn choose : (∀ [A] (Random A) => {(Tuple A A) -> (Gen A)})
  [[bounds] (Gen (λ [n r] (fst (randomR bounds r))))])

(defn variant : (∀ [A] {Integer -> (Gen A) -> (Gen A)})
  [[v (Gen m)]
   (letrec ([rands (λ [r0]
                     (case (split r0)
                       [(Tuple r1 r2)
                        {r1 :: (rands r2)}]))])
     (Gen (λ [n r]
            (m n {(rands r) !! {v + 1}}))))])

(defn promote : (∀ [A B] {{A -> (Gen B)} -> (Gen {A -> B})})
  [[f] (Gen (λ [n r]
              (λ [a]
                (case (f a)
                  [(Gen m) (m n r)]))))])

(defn sized : (∀ [A] {{Integer -> (Gen A)} -> (Gen A)})
  [[fgen] (Gen (λ [n r]
                 (case (fgen n)
                   [(Gen m) (m n r)])))])

(defn gen-bind : (∀ [A B] {(Gen A) -> {A -> (Gen B)} -> (Gen B)})
  [[(Gen m1) k]
   (Gen (λ [n r0]
              (case (split r0)
                [(Tuple r1 r2)
                 (case (k (m1 n r1))
                   [(Gen m2)
                    (m2 n r2)])])))])

(instance (Functor Gen)
  [map
   (λ [f x]
     (do [xp <- x]
         (pure (f xp))))])

(instance (Applicative Gen)
  [pure (λ [a] (Gen (λ [n r] a)))]
  [<*>
   (λ [f x]
     (do [fp <- f]
         [xp <- x]
         (pure (fp xp))))])

(instance (Monad Gen)
  [=<< (flip gen-bind)])

(defn elements : (∀ [A] {(List A) -> (Gen A)})
  [[xs]
   (map (!! xs) (choose (Tuple 0 {(length xs) - 1})))])

;; Arbitrary ; Coarbitrary

(class (Arbitrary A)
  [arbitrary : (Gen A)]
  [shrink : {A -> A}
   id])

(class (Coarbitrary A)
  [coarbitrary : (∀ [B] {A -> (Gen B) -> (Gen B)})])

(instance (Arbitrary Bool)
  [arbitrary (elements {True :: False :: Nil})])

(instance (Arbitrary Integer)
  [arbitrary (sized (λ [n] (choose (Tuple {0 - n} n))))]
  [shrink (λ [x] (quotient! x 2))])

(instance (∀ [A B] (Arbitrary A) (Arbitrary B) => (Arbitrary (Tuple A B)))
  [arbitrary (do [a <- arbitrary]
                 [b <- arbitrary]
                 (pure (Tuple a b)))]
  [shrink (λ* [[(Tuple a b)] (Tuple (shrink a) (shrink b))])])

(instance (∀ [A] (Arbitrary A) => (Arbitrary (List A)))
  [arbitrary (sized (λ [n] {(choose (Tuple 0 n)) >>= vector}))]
  [shrink
   (λ [xs] (map shrink (take (quotient! (length xs) 2) xs)))])

(instance (∀ [A B] (Coarbitrary A) (Arbitrary B) => (Arbitrary {A -> B}))
  [arbitrary (promote (λ [x] (coarbitrary x arbitrary)))])

(instance (Coarbitrary Bool)
  [coarbitrary (λ [b] (variant (if b 0 1)))])

(instance (Coarbitrary Integer)
  [coarbitrary
   (λ [n] (if {n == 0}
              (variant 0)
              (if {n < 0}
                  {(variant 2) . (coarbitrary (- n))}
                  {(variant 1) . (coarbitrary (quotient! n 2))})))])

(instance (∀ [A B] (Coarbitrary A) (Coarbitrary B) => (Coarbitrary (Tuple A B)))
  [coarbitrary
   (λ* [[(Tuple a b)]
        {(coarbitrary a) . (coarbitrary b)}])])

(instance (∀ [A B] (Coarbitrary A) => (Coarbitrary (List A)))
  [coarbitrary
   (λ* [[Nil] (variant 0)]
       [[{a :: as}] {(variant 1) . (coarbitrary a) . (coarbitrary as)}])])

(instance (∀ [A B] (Arbitrary A) (Coarbitrary B) => (Coarbitrary {A -> B}))
  [coarbitrary
   (λ [f gen]
     {arbitrary >>= {(λ [x] (coarbitrary x gen)) . f}})])

;; back to regular programming

(defn vector : (∀ [A] (Arbitrary A) => {Integer -> (Gen (List A))})
  [[n]
   (sequence (map (const arbitrary) (repeat n 1)))])

(defn oneof : (∀ [A] {(List (Gen A)) -> (Gen A)})
  [[gens] {(elements gens) >>= id}])

(defn frequency : (∀ [A] {(List (Tuple Integer (Gen A))) -> (Gen A)})
  [[xs]
   (letrec ([pick
             (λ* [[n {(Tuple k x) :: xs}]
                  (if {n <= k}
                      x
                      (pick {n - k} xs))]
                 [[_ _] undefined!])])
     (do [idx <- (choose (Tuple 1 (sum (map fst xs))))]
         (pick idx xs)))])

;; Property

(data Result
      (Result (Maybe Bool) (List String) (List String)))

(defn ok : {Result -> (Maybe Bool)}
  [[(Result m _ _)] m])

(defn stamp : {Result -> (List String)}
  [[(Result _ s _)] s])

(defn arguments : {Result -> (List String)}
  [[(Result _ _ as)] as])

(data Property
      (Prop (Gen Result)))

(def nothing : Result
  (Result Nothing Nil Nil))

(defn result : {Result -> Property}
  [[res] (Prop (pure res))])

(class (Testable A)
  [property : {A -> Property}])

(instance (Testable Bool)
  [property
   (λ [b] (result (Result (Just b) Nil Nil)))])

(instance (Testable Property)
  [property
   (λ [prop] prop)])

(instance (∀ [A B] (Arbitrary A) (Show A) (Testable B) => (Testable {A -> B}))
  [property (λ [f] (forAll arbitrary f))])

(defn evaluate : (∀ [A] (Testable A) => {A -> (Gen Result)})
  [[a] (case (property a)
         [(Prop gen) gen])])

(defn forAll : (∀ [A B] (Show A) (Testable B) => {(Gen A) -> {A -> B} -> Property})
  [[gen body]
   (letrec ([arg
             (λ [a res] (Result (ok res) (stamp res) {(show a) :: (arguments res)}))])
     (Prop (do [a <- gen]
               [res <- (evaluate (body a))]
               (pure (arg a res)))))])

(defn ==> : (∀ [A] (Testable A) => {Bool -> A -> Property})
  [[True a] (property a)]
  [[False a] (result nothing)])

(defn label : (∀ [A] (Testable A) => {String -> A -> Property})
  [[s a]
   (let ([add
          (λ [res] (Result (ok res) {s :: (stamp res)} (arguments res)))])
     (Prop (map add (evaluate a))))])

(defn classify : (∀ [A] (Testable A) => {Bool -> String -> A -> Property})
  [[True name] (label name)]
  ;; this didn't typecheck without the eta expansion
  [[False _] (λ [a] (property a))])

(defn collect : (∀ [A B] (Show A) (Testable B) => {A -> B -> Property})
  [[v] (label (show v))])

(defn quickCheck : (∀ [A] (Testable A) => {A -> (IO Unit)})
  [[a]
   (case (property a)
     [(Prop g)
      (let ([results (generate 20 g)])
        (reportResults results))])])

(defn generate : (∀ [A] {Integer -> (Gen A) -> (List A)})
  [[n (Gen g)]
   (let ([sg (StdGen -1234 1234)]
         [size 10])
     (letrec ([go
               (λ [sg n]
                 (if {n == 0}
                     Nil
                     (case (split sg)
                       [(Tuple sg1 sg2)
                        {(g size sg1) :: (go sg2 {n - 1})}])))])
       (go sg n)))])

(defn reportResults : {(List Result) -> (IO Unit)}
  [[Nil] (println "All tests passed!")]
  [[{(Result Nothing _ _) :: rs}]
   (reportResults rs)]
  [[{(Result (Just True) _ _) :: rs}]
    (reportResults rs)]
  [[{(Result (Just False) s a) :: _}]
    (println {"Test Failed: " ++ (show s) ++ " " ++ (show a)})])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def prop_RevUnit : {Integer -> Bool}
  (λ [x] {(reverse {x :: Nil}) == {x :: Nil}}))

(defn prop_RevApp : {(List Integer) -> (List Integer) -> Bool}
  [[xs ys]
   {(reverse {xs ++ ys}) == {(reverse ys) ++ (reverse xs)}}])

(defn prop_RevRev : {(List Integer) -> Bool}
  [[xs] {(reverse (reverse xs)) == xs}])

(defn prop_CompAssoc : {{Integer -> Integer} ->
                        {Integer -> Integer} ->
                        {Integer -> Integer} ->
                        Integer -> Bool}
  [[f g h x]
   {({f . {g . h}} x) == ({{f . g} . h} x)}])

(defn max : {Integer -> Integer -> Integer}
  [[x y] (if {x > y}
             x
             y)])

(defn prop_MaxLe : {Integer -> Integer -> Property}
  [[x y] {{x <= y} ==> {(max x y) == y}}])

(instance (Show {Integer -> Integer})
  [show (const "<procedure:Integer -> Integer>")])

(main (do (quickCheck prop_RevUnit)
          (quickCheck prop_RevApp)
          (quickCheck prop_RevRev)
          (quickCheck prop_CompAssoc)
          (quickCheck prop_MaxLe)))