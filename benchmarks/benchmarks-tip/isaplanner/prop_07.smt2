(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun minus (Nat Nat) Nat)
(assert
  (not (forall ((n Nat) (m Nat)) (= (minus (plus n m) n) m))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat) (y Nat))
    (= (minus x y)
      (ite (is-S x) (ite (is-S y) (minus (p x) (p y)) (S (p x))) Z))))
(check-sat)
