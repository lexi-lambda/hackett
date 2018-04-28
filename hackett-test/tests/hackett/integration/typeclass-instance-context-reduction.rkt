#lang hackett

(require hackett/private/test)

(data (F a) (F a))

; instance context should be reduced to prune (Eq (F a)) constraint
(instance (forall [a] (Eq a) (Eq (F a)) => (Eq (F a)))
  [== (λ [(F a) (F b)] {a == b})])

(test {{(F 1) == (F 1)} ==! True})
(test {{(F 1) == (F 2)} ==! False})
