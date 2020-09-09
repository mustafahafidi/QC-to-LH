(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun len (list) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun insort (Nat list) list)
(declare-fun sort (list) list)
(assert (not (forall ((xs list)) (= (len (sort xs)) (len xs)))))
(assert
  (forall ((x list))
    (= (len x) (ite (is-cons x) (S (len (tail x))) Z))))
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
(check-sat)
