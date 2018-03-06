#lang hackett

(provide (class RandomGen)
         (class Random)
         (data StdGen))

;; stand in since there are no bounded integers
(def intMinBound -12345)
(def intMaxBound 12345)

;; Minimal complete definition: 'next' and 'split'.

(class (RandomGen G)
  ;; The 'next' operation returns an 'Int' that is uniformly distributed
  ;; in the range returned by 'genRange' (including both end points),
  ;; and a new generator.
  [next : {G -> (Tuple Integer G)}]

  ;; The 'split' operation allows one to obtain two distinct random number
  ;; generators. This is very useful in functional programs (for example, when
  ;; passing a random number generator down to recursive calls), but very
  ;; little work has been done on statistically robust implementations of
  ;; 'split' (["System.Random\#Burton", "System.Random\#Hellekalek"]
  ;; are the only examples we know of).
   [split : {G -> (Tuple G G)}]


  ;; The 'genRange' operation yields the range of values returned by
  ;; the generator.
   
  ;; It is required that:
  ;;
  ;; * If @(a,b) = 'genRange' g@, then @a < b@.
  ;;
  ;; * 'genRange' always returns a pair of defined 'Int's.
  ;;
  ;; The second condition ensures that 'genRange' cannot examine its
  ;; argument, and hence the value it returns can be determined only by the
  ;; instance of 'RandomGen'.  That in turn allows an implementation to make
  ;; a single call to 'genRange' to establish a generator's range, without
  ;; being concerned that the generator returned by (say) 'next' might have
  ;; a different range to the generator passed to 'next'.
  ;;
  ;; The default definition spans the full range of 'Int'.
  [genRange : {G -> (Tuple Integer Integer)}
   (λ [_] (Tuple intMinBound intMaxBound))])


#|
The 'StdGen' instance of 'RandomGen' has a 'genRange' of at least 30 bits.

The result of repeatedly using 'next' should be at least as statistically
robust as the /Minimal Standard Random Number Generator/ described by
["System.Random\#Park", "System.Random\#Carta"].
Until more is known about implementations of 'split', all we require is
that 'split' deliver generators that are (a) not identical and
(b) independently robust in the sense just given.

The 'Show' and 'Read' instances of 'StdGen' provide a primitive way to save the
state of a random number generator.
It is required that @'read' ('show' g) == g@.

In addition, 'reads' may be used to map an arbitrary string (not necessarily one
produced by 'show') onto a value of type 'StdGen'. In general, the 'Read'
instance of 'StdGen' has the following properties: 

* It guarantees to succeed on any string. 

* It guarantees to consume only a finite portion of the string. 

* Different argument strings are likely to result in different results.

|#

(data StdGen
  (StdGen Integer Integer))

(def stdRange : (Tuple Integer Integer)
  (Tuple 1 2147483562))

(defn stdNext : {StdGen -> (Tuple Integer StdGen)}
  [[(StdGen s1 s2)]
   (letrec ([zp (if {z < 1}
                    {z + 2147483562}
                    z)]
            [z {s1pp - s2pp}]
            [k (quotient! s1 53668)]
            [s1p {40014 * {s1 - {k * 53668}} - {k * 12211}}]
            [s1pp (if {s1p < 0}
                      {s1p + 2147483563}
                      s1p)]
            [kp (quotient! s2 52774)]
            [s2p {40692 * {s2 - {kp * 52774}} - {kp * 3791}}]
            [s2pp (if {s2p < 0}
                      {s2p + 2147483399}
                      s2p)])
     (Tuple zp (StdGen s1pp s2pp)))])

(defn stdSplit : {StdGen -> (Tuple StdGen StdGen)}
  [[(StdGen s1 s2)] ;; @ pattern used
   (let ([std (StdGen s1 s2)])
     (case (snd (next std))
       [(StdGen t1 t2)
        ;; no statistical foundation for this!
        (letrec ([left (StdGen new_s1 t2)]
                 [right (StdGen t1 new_s2)]
                 [new_s1 (if {s1 == 2147483562}
                             1
                             {s1 + 1})]
                 [new_s2 (if {s2 == 1}
                             2147483398
                             {s2 - 1})])
          (Tuple left right))]))])

(instance (RandomGen StdGen)
  [next stdNext]
  #;[genRange (λ [_] stdRange)]
  [split stdSplit])

(instance (Show StdGen)
  [show (λ* [[(StdGen s1 s2)] {(show s1) ++ " " ++ (show s2)}])])

;; With a source of random number supply in hand, the 'Random' class allows the
;; programmer to extract random values of a variety of types.
;; 
;; Minimal complete definition: 'randomR' and 'random'.

(class (Random A)
  ;; Takes a range /(lo,hi)/ and a random number generator
  ;; /g/, and returns a random value uniformly distributed in the closed
  ;; interval /[lo,hi]/, together with a new generator. It is unspecified
  ;; what happens if /lo>hi/. For continuous types there is no requirement
  ;; that the values /lo/ and /hi/ are ever produced, but they may be,
  ;; depending on the implementation and the interval.
  [randomR : (∀ [G] (RandomGen G) => {(Tuple A A) -> G -> (Tuple A G)})]
  ;; The same as 'randomR', but using a default range determined by the type:
  ;;
  ;; * For bounded types (instances of 'Bounded', such as 'Char'),
  ;;   the range is normally the whole type.
  ;;
  ;; * For fractional types, the range is normally the semi-closed interval
  ;; @[0,1)@.
  ;;
  ;; * For 'Integer', the range is (arbitrarily) the range of 'Int'.
  [random  : (∀ [G] (RandomGen G) => {G -> (Tuple A G)})]

  ;; Plural variant of 'randomR', producing an infinite list of
  ;; random values instead of returning a new generator.
  ;; think more lib functions are needed for this default impl
  #;[randomRs : (∀ [G] (RandomGen G) => {(Tuple A A) -> G -> (List A)})]
  ;; randomRs ival g = build (\cons _nil -> buildRandoms cons (randomR ival) g)

  ;; Plural variant of 'random', producing an infinite list of
  ;; random values instead of returning a new generator.
  #;[randoms  : (∀ [G] (RandomGen G) => {G -> (List a)})]
  ;; randoms  g      = build (\cons _nil -> buildRandoms cons random g)
  
  ;; A variant of 'randomR' that uses the global random number generator
  ;; (see "System.Random#globalrng").
  ;; randomRIO :: (a,a) -> IO a
  ;; randomRIO range  = getStdRandom (randomR range)

  ;; A variant of 'random' that uses the global random number generator
  ;; (see "System.Random#globalrng").
  ;; randomIO  :: IO a
  ;; randomIO	   = getStdRandom random
  )

(instance (Random Integer)
  [randomR
   (λ [ival g] (randomIvalInteger ival g))]
  [random
   (λ [g] (randomR (Tuple intMinBound intMaxBound) g))])

(defn randomIvalInteger : (∀ [G] (RandomGen G) => {(Tuple Integer Integer) -> G -> (Tuple Integer G)})
  [[(Tuple l h) rng]
   (if {l > h}
       (randomIvalInteger (Tuple h l) rng)
       (case (genRange rng)
         [(Tuple genlo genhi)
          (letrec ([b {genhi - genlo + 1}]
                    ;; Probabilities of the most likely and least likely result
                   ;; will differ at most by a factor of (1 +- 1/q).  Assuming the RandomGen
                   ;; is uniform, of course

                   ;; On average, log q / log b more random values will be generated
                   ;; than the minimum
                   [q 1000]
                   [k {h - l + 1}]
                   [magtgt {k * q}]
                   [f (λ [mag v g]
                        (if {mag >= magtgt}
                            (Tuple v g)
                            (case (next g)
                              [(Tuple x gp)
                               (let ([vp {v * b + {x - genlo}}])
                                 {vp seq (f {mag * b} vp gp)})])))])
            (case (f 1 0 rng)
              [(Tuple v rngp)
               (Tuple {l + {v remainder! k}} rngp)]))]))])