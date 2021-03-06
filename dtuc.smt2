(set-logic HORN)
(set-info :status sat)
(declare-fun FUN (Int Int Int Int ) Bool)
(declare-fun SAD (Int Int Int Int ) Bool)

(assert (forall ((i Int) (j Int) (k Int) (n Int))
  (=> (and (= i 0) (= k 0)) (FUN i j k n))))
(assert (forall ((i Int) (k Int) (i1 Int) (j Int) (k1 Int) (n Int))
  (=> (and (FUN i j k n) (< i n) (= i1 (+ i 1)) (= k1 (+ k 1))) (FUN i1 j k1 n))))
(assert (forall ((j Int) (i Int) (j1 Int) (k Int) (n Int))
  (=> (and (FUN i j k n) (= i n) (= j1 n)) (SAD i j1 k n))))
(assert (forall ((k Int) (j Int) (i Int) (j1 Int) (k1 Int) (n Int))
  (=> (and (SAD i j k n) (> j 0) (= k1 (- k 1)) (= j1 (- j 1))) (SAD i j1 k1 n))))
(assert (forall ((i Int) (n Int) (j Int) (k Int))
  (=> (and (SAD i j k n) (> j 0) (not (> k 0))) false)))
(check-sat)
