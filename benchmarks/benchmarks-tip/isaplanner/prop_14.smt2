(declare-sort sk_a 0)
(declare-sort fun1 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-fun apply1 (fun1 sk_a) Bool)
(declare-fun filter (fun1 list) list)
(declare-fun append (list list) list)
(assert
  (not
    (forall ((p fun1) (xs list) (ys list))
      (= (filter p (append xs ys))
        (append (filter p xs) (filter p ys))))))
(assert
  (forall ((x fun1) (y list))
    (= (filter x y)
      (ite
        (is-cons y)
        (ite
          (apply1 x (head y)) (cons (head y) (filter x (tail y)))
          (filter x (tail y)))
        nil))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(check-sat)
