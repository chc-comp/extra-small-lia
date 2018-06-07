(set-logic HORN)
(set-info :status sat)
(declare-fun FUN (Int Int Int ) Bool)
(declare-fun SAD (Int Int Int ) Bool)

(assert (forall ((i Int) (j Int) (N Int))
  (=> (and (= i 0) (= j 0) (> N 0)) (FUN i j N))))
(assert (forall ((i Int) (j Int) (i1 Int) (j1 Int) (N Int))
  (=> (and (FUN i j N) (< j N) (= i1 (+ i 1)) (= j1 (+ j 2))) (FUN i1 j1 N))))
(assert (forall ((j Int) (i Int) (i1 Int) (j1 Int) (N Int))
  (=> (and (FUN i j N) (>= j N) (= i1 i) (= j1 1)) (SAD i1 j1 N))))
(assert (forall ((i Int) (j Int) (i1 Int) (j1 Int) (N Int))
  (=> (and (SAD i j N) (< j N) (= i1 (+ i 1)) (= j1 (+ j 2))) (SAD i1 j1 N))))
(assert (forall ((j Int) (i Int) (N Int))
  (=> (and (SAD i j N) (>= j N) (not (= i N))) false)))
(check-sat)