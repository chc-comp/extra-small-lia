(set-logic HORN)
(set-info :status sat)
(declare-fun itp1 (Int Int Int ) Bool)

(assert (forall ((x1 Int) (y1 Int) (z1 Int))
  (=> (and (= x1 0) (= y1 0) (= z1 0)) (itp1 x1 y1 z1))))
(assert (forall ((y1 Int) (x1 Int) (z1 Int) (x2 Int) (y2 Int) (z2 Int))
  (let ((a!1 (or (and (= x2 (+ x1 1)) (= y2 y1) (= z2 (+ z1 1)))
                 (and (= y2 (+ y1 1)) (= x2 x1) (= z2 (- z1 1))))))
    (=> (and (itp1 x1 y1 z1) a!1) (itp1 x2 y2 z2)))))
(assert (forall ((x1 Int) (y1 Int) (z1 Int))
  (=> (and (itp1 x1 y1 z1) (= x1 y1) (not (= z1 0))) false)))
(check-sat)

