(declare-sort sk_a 0)
(declare-sort sk_b 0)
(declare-sort fun1 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk_b) (tail2 list2)))))
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun apply1 (fun1 sk_b) sk_a)
(declare-fun take (Nat list) list)
(declare-fun take2 (Nat list2) list2)
(declare-fun map2 (fun1 list2) list)
(assert
  (not
    (forall ((n Nat) (f fun1) (xs list2))
      (= (take n (map2 f xs)) (map2 f (take2 n xs))))))
(assert
  (forall ((x Nat) (y list))
    (= (take x y)
      (ite
        (is-S x)
        (ite (is-cons y) (cons (head y) (take (p x) (tail y))) nil) nil))))
(assert
  (forall ((x Nat) (y list2))
    (= (take2 x y)
      (ite
        (is-S x)
        (ite (is-cons2 y) (cons2 (head2 y) (take2 (p x) (tail2 y))) nil2)
        nil2))))
(assert
  (forall ((x fun1) (y list2))
    (= (map2 x y)
      (ite
        (is-cons2 y) (cons (apply1 x (head2 y)) (map2 x (tail2 y))) nil))))
(check-sat)
