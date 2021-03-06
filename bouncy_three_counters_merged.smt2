(set-logic HORN)
(set-info :status sat)
(declare-fun itp1 (Int Int Int Int ) Bool)

(assert (forall ((count1 Int) (count3 Int) (count5 Int) (z1 Int))
  (=> (and (= count1 count3) (= count1 count5) (= count3 0) (= z1 count1))
      (itp1 count1 count3 count5 z1))))
(assert (forall ((count5 Int)
         (count1 Int)
         (count3 Int)
         (z1 Int)
         (count2 Int)
         (count4 Int)
         (count6 Int)
         (z2 Int))
  (let ((a!1 (or (and (= count2 (+ count1 1))
                      (= count4 count3)
                      (= count6 count5)
                      (= z2 (+ z1 1)))
                 (and (= count4 (+ count3 1))
                      (= count2 count1)
                      (= count6 count5)
                      (= z2 (- z1 1)))
                 (and (= count6 (+ count5 1))
                      (= count2 count1)
                      (= count4 count3)
                      (= z2 (+ z1 1))))))
    (=> (and (itp1 count1 count3 count5 z1) a!1) (itp1 count2 count4 count6 z2)))))
(assert (forall ((count3 Int) (count5 Int) (z1 Int) (count1 Int))
  (=> (and (itp1 count1 count3 count5 z1)
           (= count1 count3)
           (= count1 count5)
           (not (= z1 count1)))
      false)))
(check-sat)

