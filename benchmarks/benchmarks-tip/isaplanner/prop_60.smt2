(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun null (list) Bool)
(declare-fun last (list) Nat)
(declare-fun append (list list) list)
(assert
  (not
    (forall ((xs list) (ys list))
      (=> (not (null ys)) (= (last (append xs ys)) (last ys))))))
(assert (forall ((x list)) (= (null x) (not (is-cons x)))))
(assert
  (forall ((x list))
    (= (last x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x)) (last (cons (head (tail x)) (tail (tail x))))
          (head x))
        Z))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(check-sat)
