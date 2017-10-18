#lang hackett
(require (only-in racket/base module quote))

;; declares an internal PRNG type, with no data constructors.
;; actual instances are to be created by the prng-unsafe submodule.
(module prng-type hackett
  (require (only-in hackett/private/base
                    define-base-type))
  (provide PRNG)
  (define-base-type PRNG))

;; unsafe functions that create / operate on PRNG values
;; using the racket libraries
(module prng-unsafe racket/base
  (require racket/promise
           (submod ".." prng-type)
           (only-in hackett ∀ : -> Integer Double Unit Tuple tuple)
           hackett/private/prim/type-provide)

  (provide (typed-out
            [unsafe-make-prng : {Unit -> PRNG}]
            [unsafe-make-prng/seed : {Integer -> PRNG}]
            [unsafe-prng-next-integer : {Integer -> PRNG -> (Tuple Integer PRNG)}]
            [unsafe-prng-next-double : {PRNG -> (Tuple Double PRNG)}]))

  (define (unsafe-make-prng _)
    (let* ([rng (make-pseudo-random-generator)]
           [rng/v (pseudo-random-generator->vector rng)])
      rng/v))

  (define (unsafe-make-prng/seed k)
    (let ([rng (make-pseudo-random-generator)])
      (parameterize ([current-pseudo-random-generator rng])
        (random-seed (force k)))
      (pseudo-random-generator->vector rng)))

  (define ((unsafe-prng-next-integer k) rng/v)
    (let* ([rng (vector->pseudo-random-generator (force rng/v))]
           [x (random (force k) rng)])
      ((tuple x) (pseudo-random-generator->vector rng))))

  (define (unsafe-prng-next-double rng/v)
    (let* ([rng (vector->pseudo-random-generator (force rng/v))]
           [x (random rng)])
      ((tuple x) (pseudo-random-generator->vector rng))))
  )


(require 'prng-type 'prng-unsafe
         hackett/private/prim/type
         hackett/private/prim/base
         hackett/data/identity
         hackett/monad/trans)

(provide PRNG
         (class RandomGen)
         (class RandomValue)
         io-prng prng/seed
         random/below random/double random/range random random-io)


(def io-prng : (IO PRNG)
  (io (λ [w]
        (let ([prng (unsafe-make-prng unit)])
          (seq prng
               (tuple w prng))))))

(defn prng/seed : {Integer -> PRNG}
  [[k] (let ([prng (unsafe-make-prng/seed k)])
         (seq prng prng))])


(class (RandomGen g)
  [random/below : {Integer -> g -> (Tuple Integer g)}]
  [random/double : {g -> (Tuple Double g)}]
  [random/range : {Integer -> Integer -> g -> (Tuple Integer g)}
             (λ [lo hi g]
               (case (random/below (- hi lo) g)
                 [(tuple x g-) (tuple (+ lo x) g)]))])

(instance (RandomGen PRNG)
  [random/below unsafe-prng-next-integer]
  [random/double unsafe-prng-next-double])


(class (RandomValue a)
  [random : (∀ [g] (RandomGen g) => {g -> (Tuple a g)})])

(instance (RandomValue Integer)
  [random (random/below #x80000000)])

(instance (RandomValue Double)
  [random random/double])

(instance (RandomValue Bool)
  [random (λ [g] (case (random/below 2 g)
                [(tuple x g-) (tuple {x == 0} g-)]))])

(def random-io : (∀ [a] (RandomValue a) => (IO a))
  {{fst . random} <$> io-prng})


#|
(data (RandomT m a)
  (random-t (∀ [g] (RandomGen g) => {g -> (m (Tuple a g))})))

(defn run-random-t : (∀ [g m a] (RandomGen g) => {(RandomT m a) -> g -> (m (Tuple g a))})
  [[(random-t f) g] (f g)])

(defn run-random : (∀ [g m a] (RandomGen g) =>
                      {(RandomT Identity a) -> g -> (Tuple g a)})
  [[m g] (run-identity (run-random-t m g))])
|#
