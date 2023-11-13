; mod operator does not work

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and (>= a 1) (<= a 9)))
(assert (and (>= b 0) (<= b 9)))
(assert (and (>= c 1) (<= c 9)))

(assert (= 0 (mod (+ (* a 100) (* b 10) c) 4)))
(assert (= 0 (mod (+ (* c 100) (* b 10) a) 4)))

(check-sat)