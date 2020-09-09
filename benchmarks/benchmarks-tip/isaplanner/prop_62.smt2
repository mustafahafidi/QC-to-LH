(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun null (list) Bool)
(declare-fun last (list) Nat)
(assert
  (not
    (forall ((xs list) (x Nat))
      (=> (not (null xs)) (= (last (cons x xs)) (last xs))))))
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
(check-sat)
