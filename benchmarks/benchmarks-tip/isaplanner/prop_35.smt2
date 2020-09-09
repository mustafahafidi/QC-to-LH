(declare-sort sk_a 0)
(declare-sort fun1 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-const lam fun1)
(declare-fun apply1 (fun1 sk_a) Bool)
(declare-fun dropWhile (fun1 list) list)
(assert (not (forall ((xs list)) (= (dropWhile lam xs) xs))))
(assert
  (forall ((x fun1) (y list))
    (= (dropWhile x y)
      (ite
        (is-cons y)
        (ite
          (apply1 x (head y)) (dropWhile x (tail y))
          (cons (head y) (tail y)))
        nil))))
(assert (forall ((x sk_a)) (not (apply1 lam x))))
(check-sat)
