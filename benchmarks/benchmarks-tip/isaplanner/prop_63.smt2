(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun lt (Nat Nat) Bool)
(declare-fun len (list) Nat)
(declare-fun last (list) Nat)
(declare-fun drop (Nat list) list)
(assert
  (not
    (forall ((n Nat) (xs list))
      (=> (lt n (len xs)) (= (last (drop n xs)) (last xs))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (lt x y)
      (ite (is-S y) (ite (is-S x) (lt (p x) (p y)) true) false))))
(assert
  (forall ((x list))
    (= (len x) (ite (is-cons x) (S (len (tail x))) Z))))
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
  (forall ((x Nat) (y list))
    (= (drop x y)
      (ite (is-S x) (ite (is-cons y) (drop (p x) (tail y)) nil) y))))
(check-sat)
