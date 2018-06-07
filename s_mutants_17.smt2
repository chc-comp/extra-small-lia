(set-logic HORN)
(set-info :status sat)
(declare-fun itp (Int Int Int ) Bool)

(assert (forall ((x1 Int) (x3 Int) (y Int))
  (=> (and (= x1 0) (> y 0) (< y 5) (= x3 (* 3 y))) (itp x1 x3 y))))
(assert (forall ((x1 Int) (x3 Int) (x2 Int) (x4 Int) (y Int))
  (=> (and (itp x1 x3 y) (< x1 1000) (= x2 (+ x1 1)) (= x4 (+ x3 1)))
      (itp x2 x4 y))))
(assert (forall ((x1 Int) (y Int) (x3 Int))
  (let ((a!1 (and (itp x1 x3 y) (not (and (>= x3 3) (<= x3 1012))))))
    (=> a!1 false))))
(check-sat)

