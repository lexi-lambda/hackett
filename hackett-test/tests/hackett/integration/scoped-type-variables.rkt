#lang hackett

(require hackett/private/test)

(defn id : (forall [a] {a -> a})
  [[x] (: x a)])

(test {(id 42) ==! 42})
(test {(id "hello") ==! "hello"})

(test {(: (Right (: mempty b)) (forall [a b] (Monoid b) => (Either a b)))
       ==! (: (Right "") (Either Unit String))})
