(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)

(assert (and (>= a 1) (<= a 9)))
(assert (and (>= b 1) (<= b 9)))
(assert (and (>= c 1) (<= c 9)))
(assert (and (>= d 1) (<= d 9)))

(assert (= d (+ a c)))
(assert (= c (* a b)))
(assert (= b (- c b)))
(assert (= d (* a 4)))

(assert (not (and (= a 2) (= b 3) (= c 6) (= d 8))))

(check-sat)