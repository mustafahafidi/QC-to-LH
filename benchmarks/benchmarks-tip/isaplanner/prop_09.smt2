(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun minus (Nat Nat) Nat)
(assert
  (not
    (forall ((i Nat) (j Nat) (k Nat))
      (= (minus (minus i j) k) (minus i (plus j k))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat) (y Nat))
    (= (minus x y)
      (ite (is-S x) (ite (is-S y) (minus (p x) (p y)) (S (p x))) Z))))
(check-sat)
