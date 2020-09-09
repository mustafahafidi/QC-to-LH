(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-const one Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun qexp (Nat Nat Nat) Nat)
(declare-fun exp (Nat Nat) Nat)
(assert
  (not (forall ((x Nat) (y Nat)) (= (exp x y) (qexp x y one)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert (= one (S Z)))
(assert
  (forall ((x Nat) (y Nat))
    (= (mult x y) (ite (is-S x) (plus y (mult (p x) y)) Z))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (qexp x y z) (ite (is-S y) (qexp x (p y) (mult x z)) z))))
(assert
  (forall ((x Nat) (y Nat))
    (= (exp x y) (ite (is-S y) (mult x (exp x (p y))) (S Z)))))
(check-sat)
