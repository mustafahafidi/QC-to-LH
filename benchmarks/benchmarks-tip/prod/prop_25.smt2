(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun length (list) Nat)
(declare-fun even (Nat) Bool)
(declare-fun append (list list) list)
(assert
  (not
    (forall ((x list) (y list))
      (= (even (length (append x y)))
        (even (plus (length y) (length x)))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x list))
    (= (length x) (ite (is-cons x) (S (length (tail x))) Z))))
(assert
  (forall ((x Nat))
    (= (even x)
      (ite (is-S x) (ite (is-S (p x)) (even (p (p x))) false) true))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(check-sat)
