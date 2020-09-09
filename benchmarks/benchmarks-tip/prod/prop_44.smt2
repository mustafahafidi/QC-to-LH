(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun equal (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(declare-fun intersect2 (list list) list)
(assert
  (not
    (forall ((x Nat) (y list) (z list))
      (=> (elem x y) (=> (elem x z) (elem x (intersect2 y z)))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (equal x y)
      (ite
        (is-S x) (ite (is-S y) (equal (p x) (p y)) false)
        (not (is-S y))))))
(assert
  (forall ((x Nat) (y list))
    (= (elem x y)
      (ite
        (is-cons y) (or (equal x (head y)) (elem x (tail y))) false))))
(assert
  (forall ((x list) (y list))
    (= (intersect2 x y)
      (ite
        (is-cons x)
        (ite
          (elem (head x) y) (cons (head x) (intersect2 (tail x) y))
          (intersect2 (tail x) y))
        nil))))
(check-sat)
