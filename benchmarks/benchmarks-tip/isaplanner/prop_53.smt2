(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun le (Nat Nat) Bool)
(declare-fun insort (Nat list) list)
(declare-fun sort (list) list)
(declare-fun equal (Nat Nat) Bool)
(declare-fun count (Nat list) Nat)
(assert
  (not
    (forall ((n Nat) (xs list)) (= (count n xs) (count n (sort xs))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (le x y)
      (ite (is-S x) (ite (is-S y) (le (p x) (p y)) false) true))))
(assert
  (forall ((x Nat) (y list))
    (= (insort x y)
      (ite
        (is-cons y)
        (ite
          (le x (head y)) (cons x (cons (head y) (tail y)))
          (cons (head y) (insort x (tail y))))
        (cons x nil)))))
(assert
  (forall ((x list))
    (= (sort x)
      (ite (is-cons x) (insort (head x) (sort (tail x))) nil))))
(assert
  (forall ((x Nat) (y Nat))
    (= (equal x y)
      (ite
        (is-S x) (ite (is-S y) (equal (p x) (p y)) false)
        (not (is-S y))))))
(assert
  (forall ((x Nat) (y list))
    (= (count x y)
      (ite
        (is-cons y)
        (ite (equal x (head y)) (S (count x (tail y))) (count x (tail y)))
        Z))))
(check-sat)
