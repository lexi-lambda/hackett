#lang hackett/private/kernel

(require hackett/monad)

(provide (data IO)
         (data Tuple2)
         unsafe-run-io!)

(data Real-World real-world)
(data (Tuple2 a b) (tuple2 a b))
(data (IO a) (io {Real-World -> (Tuple2 Real-World a)}))

(def unsafe-run-io! : (forall [a] {(IO a) -> a})
  (λ (mf) (case mf
            [(io f) (case (f real-world)
                      [(tuple2 _ x) x])])))

(instance (Functor IO)
  [map (λ (f mio)
         (case mio
           [(io mx) (io (λ (rw)
                          (case (mx rw)
                            [(tuple2 rw* a) (tuple2 rw* (f a))])))]))])

(instance (Monad IO)
  [join (λ (m-outer)
          (case m-outer
            [(io outer)
             (io (λ (rw)
                   (case (outer rw)
                     [(tuple2 rw* m-inner)
                      (case m-inner
                        [(io inner) (inner rw*)])])))]))])

(instance (Applicative IO)
  [pure (λ (x) (io (λ (rw) (tuple2 rw x))))]
  [<*> (λ (x y) (ap x y))])
