(declare-sort sk_a 0)
(declare-sort fun1 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-const lam fun1)
(declare-fun apply1 (fun1 sk_a) Bool)
(declare-fun takeWhile (fun1 list) list)
(assert (not (forall ((xs list)) (= (takeWhile lam xs) xs))))
(assert
  (forall ((x fun1) (y list))
    (= (takeWhile x y)
      (ite
        (is-cons y)
        (ite
          (apply1 x (head y)) (cons (head y) (takeWhile x (tail y))) nil)
        nil))))
(assert (forall ((x sk_a)) (apply1 lam x)))
(check-sat)
