(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun le (Nat Nat) Bool)
(declare-fun sorted (list) Bool)
(declare-fun insort (Nat list) list)
(declare-fun sort (list) list)
(assert (not (forall ((xs list)) (sorted (sort xs)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (le x y)
      (ite (is-S x) (ite (is-S y) (le (p x) (p y)) false) true))))
(assert
  (forall ((x list))
    (= (sorted x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (and (le (head x) (head (tail x)))
            (sorted (cons (head (tail x)) (tail (tail x)))))
          true)
        true))))
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
