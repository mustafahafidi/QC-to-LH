(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun max2 (Nat Nat) Nat)
(assert (not (forall ((a Nat) (b Nat)) (= (max2 a b) (max2 b a)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (max2 x y)
      (ite (is-S x) (ite (is-S y) (S (max2 (p x) (p y))) (S (p x))) y))))
(check-sat)
