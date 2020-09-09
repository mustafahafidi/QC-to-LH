(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun length (list) Nat)
(declare-fun append (list list) list)
(declare-fun rev (list) list)
(assert
  (not
    (forall ((x list) (y list))
      (= (length (rev (append x y))) (plus (length x) (length y))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x list))
    (= (length x) (ite (is-cons x) (S (length (tail x))) Z))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(assert
  (forall ((x list))
    (= (rev x)
      (ite
        (is-cons x) (append (rev (tail x)) (cons (head x) nil)) nil))))
(check-sat)
