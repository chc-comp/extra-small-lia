(set-logic HORN)
(set-info :status sat)
(declare-fun inv (Int ) Bool)

(assert (forall ((i Int)) (=> (= i 0) (inv i))))
(assert (forall ((i Int) (i1 Int)) (=> (and (inv i) (= i1 (+ i 2))) (inv i1))))
(assert (forall ((i Int))
  (let ((a!1 (and (inv i) (not (= (mod i 2) 0)))))
    (=> a!1 false))))
(check-sat)

