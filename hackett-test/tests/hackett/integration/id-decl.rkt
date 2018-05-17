#lang hackett

(require hackett/private/test)

(: f {Integer -> Integer})
(def f (λ [x] (id x)))

(: fact {Integer -> Integer})
(defn fact 
  [[0] 1]
  [[n] {n * (fact {n - 1})}])

(: id (forall [a] {a -> a}))
(defn id
  [[x] (: x a)])

(: rmt (forall [a b] (Monoid b) => (Either a b)))
(def rmt (Right (: mempty b)))

(test {rmt ==! (: (Right "") (Either Unit String))})
(test {rmt ==! (: (Right Nil) (Either Bool (List Integer)))})

