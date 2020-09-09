(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-const one Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun qfac (Nat Nat) Nat)
(declare-fun fac (Nat) Nat)
(assert (not (forall ((x Nat)) (= (fac x) (qfac x one)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert (= one (S Z)))
(assert
  (forall ((x Nat) (y Nat))
    (= (mult x y) (ite (is-S x) (plus y (mult (p x) y)) Z))))
(assert
  (forall ((x Nat) (y Nat))
    (= (qfac x y) (ite (is-S x) (qfac (p x) (mult (S (p x)) y)) y))))
(assert
  (forall ((x Nat))
    (= (fac x) (ite (is-S x) (mult (S (p x)) (fac (p x))) (S Z)))))
(check-sat)
