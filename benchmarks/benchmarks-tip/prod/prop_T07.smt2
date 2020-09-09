(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun qrev (list list) list)
(declare-fun plus (Nat Nat) Nat)
(declare-fun length (list) Nat)
(assert
  (not
    (forall ((x list) (y list))
      (= (length (qrev x y)) (plus (length x) (length y))))))
(assert
  (forall ((x list) (y list))
    (= (qrev x y)
      (ite (is-cons x) (qrev (tail x) (cons (head x) y)) y))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x list))
    (= (length x) (ite (is-cons x) (S (length (tail x))) Z))))
(check-sat)
