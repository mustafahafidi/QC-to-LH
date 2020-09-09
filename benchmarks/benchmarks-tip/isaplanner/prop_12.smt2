(declare-sort sk_a 0)
(declare-sort sk_b 0)
(declare-sort fun1 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk_b) (tail2 list2)))))
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun apply1 (fun1 sk_b) sk_a)
(declare-fun map2 (fun1 list2) list)
(declare-fun drop (Nat list) list)
(declare-fun drop2 (Nat list2) list2)
(assert
  (not
    (forall ((n Nat) (f fun1) (xs list2))
      (= (drop n (map2 f xs)) (map2 f (drop2 n xs))))))
(assert
  (forall ((x fun1) (y list2))
    (= (map2 x y)
      (ite
        (is-cons2 y) (cons (apply1 x (head2 y)) (map2 x (tail2 y))) nil))))
(assert
  (forall ((x Nat) (y list))
    (= (drop x y)
      (ite (is-S x) (ite (is-cons y) (drop (p x) (tail y)) nil) y))))
(assert
  (forall ((x Nat) (y list2))
    (= (drop2 x y)
      (ite (is-S x) (ite (is-cons2 y) (drop2 (p x) (tail2 y)) nil2) y))))
(check-sat)
