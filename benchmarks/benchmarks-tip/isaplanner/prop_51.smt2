(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-fun butlast (list) list)
(declare-fun append (list list) list)
(assert
  (not
    (forall ((xs list) (x sk_a))
      (= (butlast (append xs (cons x nil))) xs))))
(assert
  (forall ((x list))
    (= (butlast x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (cons (head x) (butlast (cons (head (tail x)) (tail (tail x)))))
          nil)
        nil))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(check-sat)
