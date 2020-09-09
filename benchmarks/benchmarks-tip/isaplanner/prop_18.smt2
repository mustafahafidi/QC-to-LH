(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun lt (Nat Nat) Bool)
(assert (not (forall ((i Nat) (m Nat)) (lt i (S (plus i m))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat) (y Nat))
    (= (lt x y)
      (ite (is-S y) (ite (is-S x) (lt (p x) (p y)) true) false))))
(check-sat)
