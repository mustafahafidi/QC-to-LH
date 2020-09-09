(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun length (list) Nat)
(declare-fun append (list list) list)
(declare-fun rotate (Nat list) list)
(assert
  (not
    (forall ((x list) (y list))
      (= (rotate (length x) (append x y)) (append y x)))))
(assert
  (forall ((x list))
    (= (length x) (ite (is-cons x) (S (length (tail x))) Z))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(assert
  (forall ((x Nat) (y list))
    (= (rotate x y)
      (ite
        (is-S x)
        (ite
          (is-cons y) (rotate (p x) (append (tail y) (cons (head y) nil)))
          nil)
        y))))
(check-sat)
