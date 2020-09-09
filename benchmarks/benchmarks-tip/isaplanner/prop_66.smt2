(declare-sort sk_a 0)
(declare-sort fun1 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun apply1 (fun1 sk_a) Bool)
(declare-fun len (list) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun filter (fun1 list) list)
(assert
  (not
    (forall ((q fun1) (xs list)) (le (len (filter q xs)) (len xs)))))
(assert
  (forall ((x list))
    (= (len x) (ite (is-cons x) (S (len (tail x))) Z))))
(assert
  (forall ((x Nat) (y Nat))
    (= (le x y)
      (ite (is-S x) (ite (is-S y) (le (p x) (p y)) false) true))))
(assert
  (forall ((x fun1) (y list))
    (= (filter x y)
      (ite
        (is-cons y)
        (ite
          (apply1 x (head y)) (cons (head y) (filter x (tail y)))
          (filter x (tail y)))
        nil))))
(check-sat)
