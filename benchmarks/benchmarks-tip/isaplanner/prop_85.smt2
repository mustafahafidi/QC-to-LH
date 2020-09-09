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
(declare-fun len (list2) Nat)
(declare-fun len2 (list3) Nat)
(declare-fun append (list list) list)
(declare-fun append2 (list2 list2) list2)
(declare-fun append3 (list3 list3) list3)
(declare-fun rev (list) list)
(declare-fun rev2 (list2) list2)
(declare-fun rev3 (list3) list3)
(assert
  (not
    (forall ((xs list2) (ys list3))
      (=> (= (len xs) (len2 ys))
        (= (zip (rev2 xs) (rev3 ys)) (rev (zip xs ys)))))))
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
  (forall ((x list2))
    (= (len x) (ite (is-cons2 x) (S (len (tail2 x))) Z))))
(assert
  (forall ((x list3))
    (= (len2 x) (ite (is-cons3 x) (S (len2 (tail3 x))) Z))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(assert
  (forall ((x list2) (y list2))
    (= (append2 x y)
      (ite (is-cons2 x) (cons2 (head2 x) (append2 (tail2 x) y)) y))))
(assert
  (forall ((x list3) (y list3))
    (= (append3 x y)
      (ite (is-cons3 x) (cons3 (head3 x) (append3 (tail3 x) y)) y))))
(assert
  (forall ((x list))
    (= (rev x)
      (ite
        (is-cons x) (append (rev (tail x)) (cons (head x) nil)) nil))))
(assert
  (forall ((x list2))
    (= (rev2 x)
      (ite
        (is-cons2 x) (append2 (rev2 (tail2 x)) (cons2 (head2 x) nil2))
        nil2))))
(assert
  (forall ((x list3))
    (= (rev3 x)
      (ite
        (is-cons3 x) (append3 (rev3 (tail3 x)) (cons3 (head3 x) nil3))
        nil3))))
(check-sat)
