(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun equal (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(declare-fun delete (Nat list) list)
(assert
  (not (forall ((x Nat) (xs list)) (not (elem x (delete x xs))))))
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
  (forall ((x Nat) (y list))
    (= (delete x y)
      (ite
        (is-cons y)
        (ite
          (equal x (head y)) (delete x (tail y))
          (cons (head y) (delete x (tail y))))
        nil))))
(check-sat)
