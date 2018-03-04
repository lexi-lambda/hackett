#lang hackett

(require hackett/private/test)

(defn small-int? : {Integer -> Bool}
  [[0] True]
  [[1] True]
  [[2] True]
  [[_] False])

(test {(small-int? 0) ==! True})
(test {(small-int? 2) ==! True})
(test {(small-int? 4) ==! False})

(defn zero-or-none? : {(Maybe Integer) -> Bool}
  [[Nothing] True]
  [[(Just 0)] True]
  [[_] False])

(test {(zero-or-none? Nothing) ==! True})
(test {(zero-or-none? (Just 0)) ==! True})
(test {(zero-or-none? (Just 2)) ==! False})

(defn special-list? : {(List Integer) -> Bool}
  [[(:: 2 (:: n Nil))] {2 == n}]
  [[_] False])

(test {(special-list? (:: 2 (:: 2 Nil))) ==! True})
(test {(special-list? (:: 2 (:: 3 Nil))) ==! False})
(test {(special-list? (:: 3 (:: 2 Nil))) ==! False})

(defn fact : {Integer -> Integer}
  [[0] 1]
  [[n] (* n (fact (- n 1)))])

(test {(fact 2) ==! 2})
