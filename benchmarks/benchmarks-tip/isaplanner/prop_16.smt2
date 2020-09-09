(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun last (list) Nat)
(assert
  (not
    (forall ((x Nat) (xs list))
      (=> (= xs nil) (= (last (cons x xs)) x)))))
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
