(declare-sort sk_a 0)
(declare-sort sk_b 0)
(declare-datatypes ()
  ((list3 (nil3) (cons3 (head3 sk_b) (tail3 list3)))))
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk_a) (tail2 list2)))))
(declare-datatypes () ((Pair (Pair2 (first sk_a) (second sk_b)))))
(declare-datatypes ()
  ((list (nil) (cons (head Pair) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun zip (list2 list3) list)
(declare-fun drop (Nat list) list)
(declare-fun drop2 (Nat list2) list2)
(declare-fun drop3 (Nat list3) list3)
(assert
  (not
    (forall ((n Nat) (xs list2) (ys list3))
      (= (drop n (zip xs ys)) (zip (drop2 n xs) (drop3 n ys))))))
(assert
  (forall ((x list2) (y list3))
    (= (zip x y)
      (ite
        (is-cons2 x)
        (ite
          (is-cons3 y)
          (cons (Pair2 (head2 x) (head3 y)) (zip (tail2 x) (tail3 y))) nil)
        nil))))
(assert
  (forall ((x Nat) (y list))
    (= (drop x y)
      (ite (is-S x) (ite (is-cons y) (drop (p x) (tail y)) nil) y))))
(assert
  (forall ((x Nat) (y list2))
    (= (drop2 x y)
      (ite (is-S x) (ite (is-cons2 y) (drop2 (p x) (tail2 y)) nil2) y))))
(assert
  (forall ((x Nat) (y list3))
    (= (drop3 x y)
      (ite (is-S x) (ite (is-cons3 y) (drop3 (p x) (tail3 y)) nil3) y))))
(check-sat)
