(declare-sort sk_a 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk_a) (tail2 list2)))))
(declare-datatypes ()
  ((list (nil) (cons (head list2) (tail list)))))
(declare-fun append (list2 list2) list2)
(declare-fun rev (list2) list2)
(declare-fun qrevflat (list list2) list2)
(declare-fun revflat (list) list2)
(assert
  (not (forall ((x list)) (= (revflat x) (qrevflat x nil2)))))
(assert
  (forall ((x list2) (y list2))
    (= (append x y)
      (ite (is-cons2 x) (cons2 (head2 x) (append (tail2 x) y)) y))))
(assert
  (forall ((x list2))
    (= (rev x)
      (ite
        (is-cons2 x) (append (rev (tail2 x)) (cons2 (head2 x) nil2))
        nil2))))
(assert
  (forall ((x list) (y list2))
    (= (qrevflat x y)
      (ite
        (is-cons x) (qrevflat (tail x) (append (rev (head x)) y)) y))))
(assert
  (forall ((x list))
    (= (revflat x)
      (ite
        (is-cons x) (append (revflat (tail x)) (rev (head x))) nil2))))
(check-sat)
