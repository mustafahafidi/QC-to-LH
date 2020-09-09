(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-fun butlast (list) list)
(declare-fun append (list list) list)
(declare-fun butlastConcat (list list) list)
(assert
  (not
    (forall ((xs list) (ys list))
      (= (butlast (append xs ys)) (butlastConcat xs ys)))))
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
(assert
  (forall ((x list) (y list))
    (= (butlastConcat x y)
      (ite
        (is-cons y) (append x (butlast (cons (head y) (tail y))))
        (butlast x)))))
(check-sat)
