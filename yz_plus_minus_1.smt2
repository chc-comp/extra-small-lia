(set-logic HORN)
(set-info :status sat)
(declare-fun inv (Int Int Int ) Bool)

(assert (inv 0 0 0))
(assert (forall ((x Int) (z Int) (y Int) (x1 Int) (y1 Int) (z1 Int))
  (=> (and (inv x y z) (< x 100) (= x1 (+ x y)) (= y1 (+ z 1)) (= z1 (- y 1)))
      (inv x1 y1 z1))))
(assert (forall ((y Int) (z Int) (x Int)) (=> (and (inv x y z) (not (>= x 0))) false)))
(check-sat)

