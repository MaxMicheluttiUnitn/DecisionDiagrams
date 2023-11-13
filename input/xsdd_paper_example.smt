;; [(x>0) ∧ (x<1)] ∧ [(y<1) ∨ ((x>y) ∧ (y>1/2))]
(declare-fun x () Real)
(declare-fun y () Real)
(assert (and (> x 0) (< x 1)))
(assert (or (< y 1) (and (> x y) (< y 0.5))))
(check-sat)