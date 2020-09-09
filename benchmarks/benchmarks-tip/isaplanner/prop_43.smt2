(declare-sort sk_a 0)
(declare-sort fun1 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-fun apply1 (fun1 sk_a) Bool)
(declare-fun takeWhile (fun1 list) list)
(declare-fun dropWhile (fun1 list) list)
(declare-fun append (list list) list)
(assert
  (not
    (forall ((p fun1) (xs list))
      (= (append (takeWhile p xs) (dropWhile p xs)) xs))))
(assert
  (forall ((x fun1) (y list))
    (= (takeWhile x y)
      (ite
        (is-cons y)
        (ite
          (apply1 x (head y)) (cons (head y) (takeWhile x (tail y))) nil)
        nil))))
(assert
  (forall ((x fun1) (y list))
    (= (dropWhile x y)
      (ite
        (is-cons y)
        (ite
          (apply1 x (head y)) (dropWhile x (tail y))
          (cons (head y) (tail y)))
        nil))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(check-sat)
