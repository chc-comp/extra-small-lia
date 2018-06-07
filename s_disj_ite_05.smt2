(set-logic HORN)
(set-info :status sat)
(declare-fun inv (Int Int ) Bool)

(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 50)) (inv x y))))
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
  (let ((a!1 (and (inv x y)
                  (< x 100)
                  (= x2 (+ x 1))
                  (ite (> x2 50) (= y2 (+ y 1)) (= y2 y)))))
    (=> a!1 (inv x2 y2)))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (= x 100) (not (= y 100))) false)))
(check-sat)

