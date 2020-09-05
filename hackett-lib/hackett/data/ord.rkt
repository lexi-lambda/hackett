#lang hackett

(provide (data Ordering)
         (class Ord))

(require hackett/data/identity)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Ord typeclass
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(data Ordering
      lt
      eq
      gt)


(class (Eq A) => (Ord A)
  [compare : {A -> A -> Ordering}
   (λ [x y] (case* [{x le? y} {y le? x}]
              [[True True] eq]
              [[True False] lt]
              [[False True] gt]
              [[False False] (error! "Ord instance not totally ordered")]))]
  ;; <=, >=, <, and > are defined by Hackett as functions on integers and I'm not confident that I
  ;; can still write the Ord instance for integers if I shadow them here
  [le? : {A -> A -> Bool}
   (λ* [[x y] (case (compare x y) [gt False] [_ True])])]
  [ge? : {A -> A -> Bool} (λ* [[x y] (case (compare x y) [lt False] [_ True])])]
  [lt? : {A -> A -> Bool} (λ* [[x y] (case (compare x y) [lt True] [_ False])])]
  [gt? : {A -> A -> Bool} (λ* [[x y] (case (compare x y) [gt True] [_ False])])])

(instance (Ord Integer)
  [le? <=])

(instance (Ord Bool)
  [compare (λ* [[False False] eq]
               [[False True] lt]
               [[True False] gt]
               [[Tre True] eq])])

;; I couldn't find the actual implementation in Haskell but this seems to be what GHC does
(instance (∀ [A] (Ord A) => (Ord (List A)))
  [compare
   (λ* [[Nil Nil] eq]
       [[Nil _] lt]
       [[_ Nil] gt]
       [[{x :: xs} {y :: ys}]
        (case (compare x y)
          [eq (compare xs ys)]
          [ans ans])])])

(instance (∀ [A B] (Ord A) (Ord B) => (Ord (Tuple A B)))
  [compare
   (λ* [[(Tuple a1 b1) (Tuple a2 b2)]
        (case (compare a1 a2)
          [lt lt]
          [gt gt]
          [eq (compare b1 b2)])])])

(instance (∀ [A] (Ord A) => (Ord (Maybe A)))
  [le?
   (λ* [[Nothing _] True]
       [[_ Nothing] False]
       [[(Just x) (Just y)] (le? x y)])])

(instance (∀ [A B] (Ord A) (Ord B) => (Ord (Either A B)))
  [le?
   (λ* [[(Left x) (Left y)] (le? x y)]
       [[(Left _) _] True]
       [[_ (Left _)] False]
       [[(Right x) (Right y)] (le? x y)])])

(instance (∀ [A] (Ord A) => (Ord (Identity A)))
  [compare
   (λ* [[(Identity x) (Identity y)] (compare x y)])])