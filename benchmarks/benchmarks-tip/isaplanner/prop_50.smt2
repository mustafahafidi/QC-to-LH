(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun take (Nat list) list)
(declare-fun minus (Nat Nat) Nat)
(declare-fun len (list) Nat)
(declare-fun butlast (list) list)
(assert
  (not
    (forall ((xs list))
      (= (butlast xs) (take (minus (len xs) (S Z)) xs)))))
(assert
  (forall ((x Nat) (y list))
    (= (take x y)
      (ite
        (is-S x)
        (ite (is-cons y) (cons (head y) (take (p x) (tail y))) nil) nil))))
(assert
  (forall ((x Nat) (y Nat))
    (= (minus x y)
      (ite (is-S x) (ite (is-S y) (minus (p x) (p y)) (S (p x))) Z))))
(assert
  (forall ((x list))
    (= (len x) (ite (is-cons x) (S (len (tail x))) Z))))
(assert
  (forall ((x list))
    (= (butlast x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (cons (head x) (butlast (cons (head (tail x)) (tail (tail x)))))
          nil)
        nil))))
(check-sat)
