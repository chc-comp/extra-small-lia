(set-logic HORN)
(set-info :status sat)
(declare-fun itp1 (Int ) Bool)
(declare-fun itp2 (Int Int ) Bool)

(assert (itp1 0))
(assert (forall ((i0 Int)) (=> (and (itp1 i0) (< i0 256)) (itp2 i0 0))))
(assert (forall ((j0 Int) (i0 Int) (j1 Int))
  (=> (and (itp2 i0 j0) (< j0 16) (= j1 (+ j0 2))) (itp2 i0 j1))))
(assert (forall ((i0 Int) (j0 Int) (i1 Int))
  (=> (and (itp2 i0 j0) (>= j0 16) (= i1 (+ i0 j0))) (itp1 i1))))
(assert (forall ((i0 Int)) (=> (and (itp1 i0) (>= i0 256) (not (= i0 256))) false)))
(check-sat)
