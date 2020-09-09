(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun lt (Nat Nat) Bool)
(declare-fun ins (Nat list) list)
(declare-fun equal (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(assert
  (not
    (forall ((x Nat) (y Nat) (xs list))
      (=> (not (equal x y)) (= (elem x (ins y xs)) (elem x xs))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (lt x y)
      (ite (is-S y) (ite (is-S x) (lt (p x) (p y)) true) false))))
(assert
  (forall ((x Nat) (y list))
    (= (ins x y)
      (ite
        (is-cons y)
        (ite
          (lt x (head y)) (cons x (cons (head y) (tail y)))
          (cons (head y) (ins x (tail y))))
        (cons x nil)))))
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
(check-sat)
