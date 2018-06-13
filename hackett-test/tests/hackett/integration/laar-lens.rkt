#lang hackett
(require hackett/data/identity)

(data (Lens s t a b)
  (L (∀ [f] (Functor f) => {{a -> (f b)} -> {s -> (f t)}})))

(defn make-lens : (∀ [s t a b] {{s -> a} -> {s -> b -> t} -> (Lens s t a b)})
  [[get set]
   (L (λ [afb s]
        {(set s) <$> (afb (get s))}))])

(defn modify : (∀ [s t a b] {(Lens s t a b) -> {a -> b} -> {s -> t}})
  [[(L l) func s]
   (run-identity (l {Identity . func} s))])
