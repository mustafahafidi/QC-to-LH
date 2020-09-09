(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun min2 (Nat Nat) Nat)
(assert (not (forall ((a Nat) (b Nat)) (= (min2 a b) (min2 b a)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (min2 x y)
      (ite (is-S x) (ite (is-S y) (S (min2 (p x) (p y))) Z) Z))))
(check-sat)
