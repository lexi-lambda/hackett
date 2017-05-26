#lang hackett/private/kernel

(require hackett/data/tuple
         hackett/functor
         hackett/applicative
         hackett/monad
         (except-in hackett/private/adt data)
         (except-in hackett/private/class class)
         hackett/private/provide)

(provide (data IO) Real-World unsafe-run-io!)

(data Real-World real-world)
(data (IO a) (io (-> Real-World (Tuple Real-World a))))

(defn unsafe-run-io! : (∀ [a] {(IO a) -> a})
  [[(io f)] (snd (f real-world))])

(instance (Functor IO)
  [map (λ [f (io mx)]
         (io (λ [rw]
               (case (mx rw)
                 [(tuple rw* a) (tuple rw* (f a))]))))])

(instance (Applicative IO)
  [pure (λ [x] (io (λ [rw] (tuple rw x))))]
  [<*> ap])

(instance (Monad IO)
  [join (λ [(io outer)]
          (io (λ [rw]
                (case (outer rw)
                  [(tuple rw* m-inner)
                   (case m-inner
                     [(io inner)
                      (inner rw*)])]))))])
