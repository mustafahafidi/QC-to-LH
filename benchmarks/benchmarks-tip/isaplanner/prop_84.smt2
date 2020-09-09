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
(declare-fun take (Nat list2) list2)
(declare-fun len (list3) Nat)
(declare-fun drop (Nat list2) list2)
(declare-fun append (list list) list)
(declare-fun append2 (list3 list3) list3)
(assert
  (not
    (forall ((xs list2) (ys list3) (zs list3))
      (= (zip xs (append2 ys zs))
        (append (zip (take (len ys) xs) ys)
          (zip (drop (len ys) xs) zs))))))
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
  (forall ((x Nat) (y list2))
    (= (take x y)
      (ite
        (is-S x)
        (ite (is-cons2 y) (cons2 (head2 y) (take (p x) (tail2 y))) nil2)
        nil2))))
(assert
  (forall ((x list3))
    (= (len x) (ite (is-cons3 x) (S (len (tail3 x))) Z))))
(assert
  (forall ((x Nat) (y list2))
    (= (drop x y)
      (ite (is-S x) (ite (is-cons2 y) (drop (p x) (tail2 y)) nil2) y))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(assert
  (forall ((x list3) (y list3))
    (= (append2 x y)
      (ite (is-cons3 x) (cons3 (head3 x) (append2 (tail3 x) y)) y))))
(check-sat)
