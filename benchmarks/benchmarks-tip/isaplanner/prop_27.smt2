(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun equal (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(declare-fun append (list list) list)
(assert
  (not
    (forall ((x Nat) (xs list) (ys list))
      (=> (elem x ys) (elem x (append xs ys))))))
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
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(check-sat)
