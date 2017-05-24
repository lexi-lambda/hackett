#lang hackett/private/kernel

(require (only-in racket/base for-syntax)
         (for-syntax racket/base
                     syntax/parse/class/paren-shape)
         hackett/data/tuple
         hackett/functor
         hackett/applicative
         hackett/monad
         (except-in hackett/private/adt data)
         (except-in hackett/private/class class)
         hackett/private/provide
         syntax/parse/define)

(provide (data IO) Real-World unsafe-run-io!)

(data Real-World real-world)
(data (IO a) (io (-> Real-World (Tuple Real-World a))))

(def unsafe-run-io! : (∀ [a] {(IO a) -> a})
  (λ [mf] (case mf [(io f) (snd (f real-world))])))

(instance (Functor IO)
  [map (λ [f mio]
         (case mio
           [(io mx) (io (λ [rw]
                          (case (mx rw)
                            [(tuple rw* a) (tuple rw* (f a))])))]))])

(instance (Applicative IO)
  [pure (λ [x] (io (λ [rw] (tuple rw x))))]
  [<*> (λ [f] (ap f))])

(instance (Monad IO)
  [join (λ [m-outer]
          (case m-outer
            [(io outer)
             (io (λ [rw]
                   (case (outer rw)
                     [(tuple rw* m-inner)
                      (case m-inner
                        [(io inner)
                         (inner rw*)])])))]))])
