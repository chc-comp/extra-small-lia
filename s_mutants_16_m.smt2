(set-logic HORN)
(set-info :status sat)
(declare-fun itp (Int Int Int ) Bool)
(declare-fun itp1 (Int Int Int ) Bool)

(assert (forall ((x1 Int) (x3 Int) (y Int))
  (=> (and (= x1 0) (> y 0) (< y 5) (= x3 (* 3 y))) (itp x1 x3 y))))
(assert (forall ((x1 Int) (x3 Int) (x2 Int) (x4 Int) (y Int))
  (=> (and (itp x1 x3 y) (< x1 100) (= x2 (+ x1 1)) (= x4 (+ x3 1)))
      (itp x2 x4 y))))
(assert (forall ((x1 Int) (x3 Int) (y Int))
  (=> (and (itp x1 x3 y) (not (< x1 100))) (itp1 x1 x3 y))))
(assert (forall ((x1 Int) (x3 Int) (x2 Int) (x4 Int) (y Int))
  (=> (and (itp1 x1 x3 y) (< x1 120) (= x2 (+ x1 1)) (= x4 (+ x3 1)))
      (itp1 x2 x4 y))))
(assert (forall ((y Int) (x1 Int) (x3 Int))
  (let ((a!1 (and (itp1 x1 x3 y)
                  (not (< x1 120))
                  (not (and (>= x3 3) (<= x3 132))))))
    (=> a!1 false))))
(check-sat)
