(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun half (Nat) Nat)
(assert (not (forall ((x Nat)) (= (half (plus x x)) x))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat))
    (= (half x)
      (ite (is-S x) (ite (is-S (p x)) (S (half (p (p x)))) Z) Z))))
(check-sat)
