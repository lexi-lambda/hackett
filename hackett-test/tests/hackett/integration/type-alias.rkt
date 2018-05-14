#lang hackett

(require hackett/private/test
         (only-in racket/base submod)
         (submod tests/hackett/typecheck assertions))

(type X Integer)
(def x : X 5)
(typecheck-fail (: "" X))

(type (Arr a b) {a -> b})
(type (Pred a) (Arr a Bool))
(type (BiRel a) {a -> a -> Bool})

(type Y (forall [a b] (Monoid b) => (Either a b)))

(typecheck-fail
 (λ ([x : (Arr Bool)]) ; not enough args to alias
   x))

(defn never : (forall [a] (Pred a))
  [[x] False])

(test {(never 5) ==! False})
(test {(never "asdasaf") ==! False})

(def int= : (BiRel Integer)
  ==)

(test {{4 int= 6} ==! False})
(test {{4 int= 4} ==! True})
