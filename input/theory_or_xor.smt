(declare-fun x () Int)

(assert (xor (<= x 0) (= x 1)))

(check-sat)