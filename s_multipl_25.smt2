(set-logic HORN)
(set-info :status sat)
(declare-fun inv1 (Int Int Int Int ) Bool)
(declare-fun inv2 (Int Int Int Int ) Bool)

(assert (forall ((x Int) (y Int) (i Int) (j Int))
  (=> (and (= x 0) (= y 0) (= i 0) (= j 0)) (inv1 x y i j))))
(assert (forall ((i Int) (x Int) (y Int) (x1 Int) (y1 Int) (i1 Int) (j Int))
  (=> (and (inv1 x y i j) (= i1 (+ i 1)) (= x1 (+ x i1)) (= y1 (- y i1)))
      (inv1 x1 y1 i1 j))))
(assert (forall ((x Int) (y Int) (i Int) (j Int)) (=> (inv1 x y i j) (inv2 x y i j))))
(assert (forall ((j Int) (x Int) (y Int) (x1 Int) (y1 Int) (i Int) (j1 Int))
  (=> (and (inv2 x y i j) (= j1 (+ j 1)) (= x1 (- x j1)) (= y1 (+ y j1)))
      (inv2 x1 y1 i j1))))
(assert (forall ((i Int) (j Int) (x Int) (y Int))
  (=> (and (inv2 x y i j) (> i j) (not (> x y))) false)))
(check-sat)
