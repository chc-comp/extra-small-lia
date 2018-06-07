(set-logic HORN)
(set-info :status sat)
(declare-fun inv (Int Int ) Bool)

(assert (forall ((i Int) (j Int)) (=> (and (= i 0) (= j 0)) (inv i j))))
(assert (forall ((i Int) (j Int) (i1 Int) (j1 Int))
  (let ((a!1 (and (inv i j) (= i1 (+ i 1)) (= j1 (ite (= j 0) 1 0)))))
    (=> a!1 (inv i1 j1)))))
(assert (forall ((j Int) (i Int))
  (let ((a!1 (not (ite (= j 1) (= (mod i 2) 1) (= (mod i 2) 0)))))
    (=> (and (inv i j) a!1) false))))
(check-sat)

