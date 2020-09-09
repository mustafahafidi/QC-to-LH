(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun len (list) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun equal (Nat Nat) Bool)
(declare-fun delete (Nat list) list)
(assert
  (not
    (forall ((n Nat) (xs list)) (le (len (delete n xs)) (len xs)))))
(assert
  (forall ((x list))
    (= (len x) (ite (is-cons x) (S (len (tail x))) Z))))
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
