(declare-const a Int)
(declare-const b Int)

(assert (and (>= a 1) (<= a 8)))
(assert (and (>= b 1) (<= b 8)))

(assert (not (= a b)))

(check-sat)