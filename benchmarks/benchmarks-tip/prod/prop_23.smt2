(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun length (list) Nat)
(declare-fun half (Nat) Nat)
(declare-fun append (list list) list)
(assert
  (not
    (forall ((x list) (y list))
      (= (half (length (append x y))) (half (length (append y x)))))))
(assert
  (forall ((x list))
    (= (length x) (ite (is-cons x) (S (length (tail x))) Z))))
(assert
  (forall ((x Nat))
    (= (half x)
      (ite (is-S x) (ite (is-S (p x)) (S (half (p (p x)))) Z) Z))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(check-sat)
