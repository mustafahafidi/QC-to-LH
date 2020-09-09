(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun min2 (Nat Nat) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun equal (Nat Nat) Bool)
(assert
  (not (forall ((a Nat) (b Nat)) (= (equal (min2 a b) a) (le a b)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (min2 x y)
      (ite (is-S x) (ite (is-S y) (S (min2 (p x) (p y))) Z) Z))))
(assert
  (forall ((x Nat) (y Nat))
    (= (le x y)
      (ite (is-S x) (ite (is-S y) (le (p x) (p y)) false) true))))
(assert
  (forall ((x Nat) (y Nat))
    (= (equal x y)
      (ite
        (is-S x) (ite (is-S y) (equal (p x) (p y)) false)
        (not (is-S y))))))
(check-sat)
