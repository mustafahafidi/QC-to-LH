(declare-sort sk_a 0)
(declare-datatypes ()
  ((Tree (Leaf) (Node (Node_0 Tree) (Node_1 sk_a) (Node_2 Tree)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun mirror (Tree) Tree)
(declare-fun max2 (Nat Nat) Nat)
(declare-fun height (Tree) Nat)
(assert
  (not (forall ((b Tree)) (= (height (mirror b)) (height b)))))
(assert
  (forall ((x Tree))
    (= (mirror x)
      (ite
        (is-Node x)
        (Node (mirror (Node_2 x)) (Node_1 x) (mirror (Node_0 x))) Leaf))))
(assert
  (forall ((x Nat) (y Nat))
    (= (max2 x y)
      (ite (is-S x) (ite (is-S y) (S (max2 (p x) (p y))) (S (p x))) y))))
(assert
  (forall ((x Tree))
    (= (height x)
      (ite
        (is-Node x) (S (max2 (height (Node_0 x)) (height (Node_2 x))))
        Z))))
(check-sat)
