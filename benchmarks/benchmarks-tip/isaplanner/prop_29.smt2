(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun equal (Nat Nat) Bool)
(declare-fun ins1 (Nat list) list)
(declare-fun elem (Nat list) Bool)
(assert (not (forall ((x Nat) (xs list)) (elem x (ins1 x xs)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (equal x y)
      (ite
        (is-S x) (ite (is-S y) (equal (p x) (p y)) false)
        (not (is-S y))))))
(assert
  (forall ((x Nat) (y list))
    (= (ins1 x y)
      (ite
        (is-cons y)
        (ite
          (equal x (head y)) (cons (head y) (tail y))
          (cons (head y) (ins1 x (tail y))))
        (cons x nil)))))
(assert
  (forall ((x Nat) (y list))
    (= (elem x y)
      (ite
        (is-cons y) (or (equal x (head y)) (elem x (tail y))) false))))
(check-sat)
