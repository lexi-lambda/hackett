#lang hackett

#|
 | Access to Racket's random number generators.
 |
 | Instead of using Racket's idea of the "current" generator, which would involve side effects,
 | we'll isolate each generator into a 'PRNG' monad, 'Pseudo-Random Number Generator'.
 |
 | NOTE: Racket allows multiple different generators to exist independently, as we want.
 | But, the 'random-seed' function only works on the 'current' generator. As a result,
 | to do seeding in this library, we need to temporarily store a reference to the old 'current'
 | generator, before applying the seed to our generator of interest, then reset it again.
 | See 'raw-make-prng' for how this is done.
 |
 | Example:
 |
 |          (def one.dice (random-integer 1 7))       ; one roll of a dice
 |          (def many.dice : (PRNG (List Integer))    ; 100 rolls
 |              (replicate-random 100 one.dice))
 |          (main
 |              { many.dice  & run-prng & show & println }) ; 'run-prng' runs the monad, seeded with '(random-seed 1)' and is therefore "deterministic"
 |
 |          ; if you want a different seed
 |          (main
 |              { (do (set-seed 1337)
 |                    many.dice
 |                )
 |                  & run-prng & show & println }) ; 'run-prng' runs the monad, seeded with '(random-seed 1)' and is therefore "deterministic"
 |
 |
 | Implementation:
 |
 | First, we need a way to 'store' such a generator, once it has been created. We do this
 | using the 'Random-World' data type, where three (Racket) functions are stored. There
 | are three functions, one for each 'method' we would wish to call on a generator:
 | set the seed, draw a random double, draw a random integer. This means that we don't
 | need a Hackett datatype to directly represent the state of a generator.
 |
 | This 'Random-World' shouldn't be copyable by users, as calls through one copy would
 | be visible through other copies. Therefore, we create a Monad called PRNG which
 | stores a function of this type:   {Random-World -> (Tuple Random-World a)}
 |
 | Structure of this file:
 |  - first, (provide) a few things to the outside world.
 |  - next, a "(module shared hackett)" module with some declarations that are needed
 |        by both the untyped and typed code. Mostly private to this file.
 |  - then, a "(module untyped racket/base" module to implement the low-level stuff taking to Racket
 |  - finally, some Hackett code to provide the necessary instances, Functor, Applicative, and Monad,
 |    and the implementation of 'run-prng'.
 |
 |
 | (Initial implementation, Oct 2017: Aaron McDaid aaron.mcdaid@gmail.com)
 |#

(require (only-in racket/base all-from-out for-syntax module submod))

(provide PRNG set-seed random-integer random-double run-prng)

(module shared hackett
    (provide
        (data PRNG)
        (data Random-World)
        get-doubler
        get-integerer
        get-seeder
        random-world
    )
    (data Random-World (random-world
                            {Integer -> Unit}               ; the seeder
                            {Unit -> Double}                ; "returns a random inexact number between 0 and 1, exclusive."
                            {Integer -> Integer -> Integer} ; "returns a random exact integer in the range min to max-1."
                            ))
    (data (PRNG a) (prng (-> Random-World (Tuple Random-World a))))
    (defn get-doubler : { Random-World -> {Unit -> Double} }
        [[(random-world seeder doubler integerer)] doubler ])
    (defn get-integerer : { Random-World -> {Integer -> Integer -> Integer} }
        [[(random-world seeder doubler integerer)] integerer ])
    (defn get-seeder  : { Random-World -> {Integer -> Unit} }
        [[(random-world seeder doubler integerer)] seeder ])
)


(module untyped racket/base
  (require hackett/private/util/require

           (prefix-in hackett: (combine-in hackett (submod ".." shared)))
           (postfix-in - (combine-in 2htdp/universe pict racket/base racket/match racket/promise))

           (only-in hackett ∀ : -> Integer Double IO Unit unit)
           hackett/private/prim/type-provide
           threading)

  (provide (typed-out           ; Only the first three of these four are re-provided to the outside world
            [random-double      : (hackett:PRNG Double)]
            [random-integer     : {Integer -> Integer -> (hackett:PRNG Integer)}]
            [set-seed           : {Integer -> (hackett:PRNG Unit)}]
            [raw-make-prng      : {Unit -> hackett:Random-World}]
            ))

  (define (raw-make-prng _)
    (let (  [my-rng (make-pseudo-random-generator)]
        )
        (((hackett:random-world ; the three lambdas on the next three lines define the three functions needed for the interface to a generator
            (λ- (seed) (let ([old-rng (current-pseudo-random-generator) ])
                        (begin
                            (current-pseudo-random-generator my-rng)
                            (random-seed seed)                        ; seed the 'current' rng, i.e. 'my-rng'
                            (current-pseudo-random-generator old-rng) ; reset the 'current' rng, as it was stored a couple of lines ago
                            hackett:unit
                            ))))
                (λ- (_) (real->double-flonum- (random- my-rng))))
                    (λ- (min) (λ- (max) (random- min max my-rng))))))

  (define (set-seed seed)
    (hackett:prng (λ- (rw) ((hackett:tuple rw)
            ((hackett:get-seeder rw) (force- seed))
    ))))

  (define random-double
    (hackett:prng (λ- (rw) ((hackett:tuple rw)
            ((hackett:get-doubler rw) unit)
    ))))

  (define ((random-integer low) upp)
    (hackett:prng (λ- (rw) ((hackett:tuple rw)
            (((hackett:get-integerer rw) low) upp)
    ))))

)

;; -- end with typed code. This means me must first 'require' the 'submod's above

(require (for-syntax racket/base)
         syntax/parse/define

         (submod "." shared)
         (submod "." untyped))

(instance (Functor PRNG)
    [map    (  λ   [f (prng mx)]   (prng (λ [rw] (case (mx rw) [(tuple rw* a) (tuple rw* (f a))])))) ])
(instance (Applicative PRNG)
    [pure (λ [x] (prng (λ [rw] (tuple rw x)))) ]
    [<*>  ap ])
(instance (Monad PRNG)
    [join (λ [(prng outer)]
        (prng (λ [rw]
        (case (outer rw)
        [(tuple rw* m-inner)
        (case m-inner
        [(prng inner)
        (inner rw*)])]))))])

(defn run-prng* : (forall [a] { (PRNG a) -> a })
    [[(prng f)]
        (case
            (f (raw-make-prng unit))    ; create a new prng, via 'raw-make-prng', then pass it to the monadic function to get its output
            [(tuple rw* a) a]           ; the output is a tuple, but we only care about the second part.
        ) ])

(defn run-prng  : (forall [a] { (PRNG a) -> a })
    [[x]
        (run-prng* (do (set-seed 1) x))
         ])
