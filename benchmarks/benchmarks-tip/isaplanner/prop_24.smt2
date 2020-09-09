(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun max2 (Nat Nat) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun equal (Nat Nat) Bool)
(assert
  (not (forall ((a Nat) (b Nat)) (= (equal (max2 a b) a) (le b a)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (max2 x y)
      (ite (is-S x) (ite (is-S y) (S (max2 (p x) (p y))) (S (p x))) y))))
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
