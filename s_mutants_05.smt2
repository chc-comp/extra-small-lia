(set-logic HORN)
(set-info :status sat)
(declare-fun itp (Int Int ) Bool)

(assert (forall ((x1 Int) (x3 Int)) (=> (and (= x1 0) (> x3 x1)) (itp x1 x3))))
(assert (forall ((x1 Int) (x3 Int) (x2 Int) (x4 Int))
  (=> (and (itp x1 x3) (= x2 (+ x1 1)) (= x4 (+ x3 2))) (itp x2 x4))))
(assert (forall ((x1 Int) (x3 Int))
  (=> (and (itp x1 x3) (> x1 1000) (not (> x3 2000))) false)))
(check-sat)

