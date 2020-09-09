(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun lt (Nat Nat) Bool)
(declare-fun len (list) Nat)
(declare-fun ins (Nat list) list)
(assert
  (not
    (forall ((x Nat) (xs list)) (= (len (ins x xs)) (S (len xs))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (lt x y)
      (ite (is-S y) (ite (is-S x) (lt (p x) (p y)) true) false))))
(assert
  (forall ((x list))
    (= (len x) (ite (is-cons x) (S (len (tail x))) Z))))
(assert
  (forall ((x Nat) (y list))
    (= (ins x y)
      (ite
        (is-cons y)
        (ite
          (lt x (head y)) (cons x (cons (head y) (tail y)))
          (cons (head y) (ins x (tail y))))
        (cons x nil)))))
(check-sat)
