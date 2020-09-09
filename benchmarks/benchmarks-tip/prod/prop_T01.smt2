(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun double (Nat) Nat)
(assert (not (forall ((x Nat)) (= (double x) (plus x x)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat))
    (= (double x) (ite (is-S x) (S (S (double (p x)))) Z))))
(check-sat)
