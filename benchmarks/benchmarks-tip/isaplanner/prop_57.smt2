(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun take (Nat list) list)
(declare-fun minus (Nat Nat) Nat)
(declare-fun drop (Nat list) list)
(assert
  (not
    (forall ((n Nat) (m Nat) (xs list))
      (= (drop n (take m xs)) (take (minus m n) (drop n xs))))))
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
  (forall ((x Nat) (y list))
    (= (drop x y)
      (ite (is-S x) (ite (is-cons y) (drop (p x) (tail y)) nil) y))))
(check-sat)
