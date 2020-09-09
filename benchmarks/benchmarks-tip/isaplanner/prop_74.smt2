(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun take (Nat list) list)
(declare-fun minus (Nat Nat) Nat)
(declare-fun len (list) Nat)
(declare-fun drop (Nat list) list)
(declare-fun append (list list) list)
(declare-fun rev (list) list)
(assert
  (not
    (forall ((i Nat) (xs list))
      (= (rev (take i xs)) (drop (minus (len xs) i) (rev xs))))))
(assert
  (forall ((x Nat) (y list))
    (= (take x y)
      (ite
        (is-S x)
        (ite (is-cons y) (cons (head y) (take (p x) (tail y))) nil) nil))))
(assert
  (forall ((x Nat) (y Nat))
    (= (minus x y)
      (ite (is-S x) (ite (is-S y) (minus (p x) (p y)) (S (p x))) Z))))
(assert
  (forall ((x list))
    (= (len x) (ite (is-cons x) (S (len (tail x))) Z))))
(assert
  (forall ((x Nat) (y list))
    (= (drop x y)
      (ite (is-S x) (ite (is-cons y) (drop (p x) (tail y)) nil) y))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(assert
  (forall ((x list))
    (= (rev x)
      (ite
        (is-cons x) (append (rev (tail x)) (cons (head x) nil)) nil))))
(check-sat)
