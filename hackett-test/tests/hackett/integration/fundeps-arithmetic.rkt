#lang hackett

(require hackett/private/test)

(data (Proxy t) Proxy)

(data Z)
(data (S n))

(defn sub1/Nat : (forall [n] {(Proxy (S n)) -> (Proxy n)})
  [[_] Proxy])

(class (Reify-Nat n)
  [reify-nat : {(Proxy n) -> Integer}])
(instance (Reify-Nat Z)
  [reify-nat (λ [_] 0)])
(instance (forall [n] (Reify-Nat n) => (Reify-Nat (S n)))
  [reify-nat (λ [p] {1 + (reify-nat (sub1/Nat p))})])

(class (Add a b c) #:fundeps [[a b -> c]])
(instance (forall [a] (Add Z a a)))
(instance (forall [a b c] (Add a b c) => (Add (S a) b (S c))))

(class (Fib a b) #:fundeps [[a -> b]])
(instance (Fib Z Z))
(instance (Fib (S Z) (S Z)))
(instance (forall [a b c d] (Fib a b) (Fib (S a) c) (Add b c d) => (Fib (S (S a)) d)))

(defn fib : (forall [a b] (Fib a b) => {(Proxy a) -> (Proxy b)})
  [[_] Proxy])

(test {(reify-nat (fib {Proxy : (Proxy Z)})) ==! 0})
(test {(reify-nat (fib {Proxy : (Proxy (S Z))})) ==! 1})
(test {(reify-nat (fib {Proxy : (Proxy (S (S Z)))})) ==! 1})
(test {(reify-nat (fib {Proxy : (Proxy (S (S (S Z))))})) ==! 2})
(test {(reify-nat (fib {Proxy : (Proxy (S (S (S (S Z)))))})) ==! 3})
(test {(reify-nat (fib {Proxy : (Proxy (S (S (S (S (S Z))))))})) ==! 5})
(test {(reify-nat (fib {Proxy : (Proxy (S (S (S (S (S (S Z)))))))})) ==! 8})
