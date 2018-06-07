(set-logic HORN)
(set-info :status sat)
(declare-fun itp (Int Int Int ) Bool)

(assert (forall ((x9 Int) (x1 Int) (x3 Int) (x5 Int))
  (=> (and (= x1 0) (= x3 0) (= x5 (* 2 x9))) (itp x1 x3 x5))))
(assert (forall ((x1 Int) (x3 Int) (x5 Int) (x2 Int) (x4 Int) (x6 Int))
  (let ((a!1 (or (and (= x2 (+ x1 1)) (= x4 (+ x3 1)))
                 (and (= x2 (- x1 1)) (= x4 (- x3 1))))))
    (=> (and (itp x1 x3 x5) a!1 (= x6 (+ x5 x2 x4))) (itp x2 x4 x6)))))
(assert (forall ((x1 Int) (x3 Int) (x5 Int)) (=> (and (itp x1 x3 x5) (= x5 77)) false)))
(check-sat)

