#lang hackett/private/kernel

(require (only-in racket/base for-syntax except-in)
         (for-syntax racket/base
                     syntax/parse/class/paren-shape)
         hackett/data/tuple
         (except-in hackett/private/adt data)
         hackett/private/provide
         syntax/parse/define)

(provide (data IO) Real-World unsafe-run-io! pure/io map/io join/io and-then/io do/io)

(data Real-World real-world)
(data (IO a) (io (-> Real-World (Tuple Real-World a))))

(def unsafe-run-io! : (∀ [a] (-> (IO a) a))
  (λ [mf] (case mf [(io f) (snd (f real-world))])))

(def pure/io : (∀ [a] (-> a (IO a)))
  (λ [x] (io (λ [rw] (tuple rw x)))))

(def map/io : (∀ [a b] (-> (-> a b) (-> (IO a) (IO b))))
  (λ [f mio]
    (case mio
      [(io mx) (io (λ [rw]
                     (case (mx rw)
                       [(tuple rw* a) (tuple rw* (f a))])))])))

(def join/io : (∀ [a] (-> (IO (IO a)) (IO a)))
  (λ [m-outer]
    (case m-outer
      [(io outer)
       (io (λ [rw]
             (case (outer rw)
               [(tuple rw* m-inner)
                (case m-inner
                  [(io inner)
                   (inner rw*)])])))])))

(def and-then/io : (∀ [a b] (-> (IO a) (-> (-> a (IO b)) (IO b))))
  (λ [m f] (join/io (map/io f m))))

(define-syntax-parser do/io
  #:datum-literals [<-]
  [(_ e:expr)
   #'e]
  [(_ [~brackets ~! x:id <- e:expr] rest ...+)
   #'(and-then/io e (λ [x] (do/io rest ...)))]
  [(_ e:expr rest ...+)
   #'(and-then/io e (λ [_] (do/io rest ...)))])
