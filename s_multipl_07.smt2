(set-logic HORN)
(set-info :status sat)
(declare-fun FUN (Int Int ) Bool)
(declare-fun SAD (Int Int ) Bool)

(assert (forall ((k Int) (j Int)) (=> (and (= k 0) (= j 0)) (FUN k j))))
(assert (forall ((k Int) (j Int) (k1 Int) (j1 Int))
  (=> (and (FUN k j) (< j 1000) (= k1 (+ k 1)) (= j1 (+ j 1))) (FUN k1 j1))))
(assert (forall ((j Int) (k Int) (k1 Int) (j1 Int))
  (=> (and (FUN k j) (>= j 1000) (= k1 k) (= j1 0)) (SAD k1 j1))))
(assert (forall ((k Int) (j Int) (k1 Int) (j1 Int))
  (=> (and (SAD k j) (< j 1000) (= k1 (+ k 1)) (= j1 (+ j 1))) (SAD k1 j1))))
(assert (forall ((j Int) (k Int)) (=> (and (SAD k j) (>= j 1000) (< k 2000)) false)))
(check-sat)
