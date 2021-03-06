(set-logic HORN)
(set-info :status sat)
(declare-fun inv (Int Int Int Int ) Bool)

(assert (forall ((x Int) (y Int) (z Int) (i Int))
  (=> (and (> y 1) (= (mod y 2) 0) (= z 1) (> x 0) (>= i x)) (inv x y z i))))
(assert (forall ((x Int) (y Int) (z Int) (i Int) (x1 Int) (y1 Int) (z1 Int) (i1 Int))
  (=> (and (inv x y z i)
           (> x 0)
           (= x1 (- x y))
           (= y1 (- y z))
           (= z1 (- z))
           (= i1 (- i 1)))
      (inv x1 y1 z1 i1))))
(assert (forall ((y Int) (z Int) (x Int) (i Int))
  (=> (and (inv x y z i) (> x 0) (< i 0)) false)))
(check-sat)

