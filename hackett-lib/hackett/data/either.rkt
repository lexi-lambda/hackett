#lang hackett/base

(require hackett/private/prim)

(provide (data Either) either)

(defn either : (∀ [a b c] {{a -> c} -> {b -> c} -> (Either a b) -> c})
  [[f _ (left  x)] (f x)]
  [[_ g (right y)] (g y)])
