(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun even (Nat) Bool)
(assert
  (not
    (forall ((x Nat) (y Nat))
      (= (even (plus x y)) (even (plus y x))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat))
    (= (even x)
      (ite (is-S x) (ite (is-S (p x)) (even (p (p x))) false) true))))
(check-sat)
