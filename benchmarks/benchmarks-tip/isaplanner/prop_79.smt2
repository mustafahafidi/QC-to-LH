(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun minus (Nat Nat) Nat)
(assert
  (not
    (forall ((m Nat) (n Nat) (k Nat))
      (= (minus (minus (S m) n) (S k)) (minus (minus m n) k)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (minus x y)
      (ite (is-S x) (ite (is-S y) (minus (p x) (p y)) (S (p x))) Z))))
(check-sat)
