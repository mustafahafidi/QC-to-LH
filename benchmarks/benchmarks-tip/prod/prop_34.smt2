(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult2 (Nat Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(assert
  (not (forall ((x Nat) (y Nat)) (= (mult x y) (mult2 x y Z)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (mult2 x y z) (ite (is-S x) (mult2 (p x) y (plus y z)) z))))
(assert
  (forall ((x Nat) (y Nat))
    (= (mult x y) (ite (is-S x) (plus y (mult (p x) y)) Z))))
(check-sat)
