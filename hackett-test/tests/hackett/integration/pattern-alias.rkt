#lang hackett
(require hackett/private/test)

;; Exp* is like an "Exp/recur"

(data (Exp* e)
  (Var* String)
  (App* e e)
  (Lam* String e)
  #:deriving [Show])

(instance (Functor Exp*)
  [<$>
   (λ* [[f (Var* x)] (Var* x)]
       [[f (App* a b)] (App* (f a) (f b))]
       [[f (Lam* x a)] (Lam* x (f a))])])

#;
(instance (forall [e] (Show e) => (Show (Exp* e)))
  [show
   (λ* [[(Var* x)] {"(Var " ++ (show x) ++ ")"}]
       [[(App* a b)] {"(App " ++ (show a) ++ " " ++ (show b) ++ ")"}]
       [[(Lam* x a)] {"(Lam " ++ (show x) ++ " " ++ (show a) ++ ")"}])])

;; ------------------------------------------

(data Exp
  (E (Exp* Exp)))

(instance (Show Exp)
  [show (λ* [[(E e)] (show e)])])

(pattern (Var x)   (E (Var* x)))
(pattern (App a b) (E (App* a b)))
(pattern (Lam x a) (E (Lam* x a)))

(def example : Exp
  (App (Var "x")
       (Var "y")))

(defn getVar : {Exp -> String}
  [[(Var x)] x]
  [[_] (error! "not a variable")])

(defn free : {Exp -> (List String)}
    [[(Var x)] (List x)]
    [[(App f a)] {(free f) ++ (free a)}]
    [[(Lam x b)] (filter (/= x) (free b))])

;; ------------------------------------------

(test {(show example) ==! "(App* (Var* \"x\") (Var* \"y\"))"})
(test {(getVar (Var "z")) ==! "z"})
(test {(getVar (E (Var* "z"))) ==! "z"})

(test {(free (Var "x")) ==! (List "x")})
(test {(free (App (Lam "x" (App (Var "x") (Var "y")))
                  (Lam "z" (App (Var "a") (Var "z")))))
       ==!
       (List "y" "a")})

