
(declare-const d Int)
(declare-const e Int)
(declare-const f Int)
(declare-const g Int)

(assert (= d 0))
(assert (or (= e (+ d 3)) (= e (+ g 11))))
(assert (or (= f (+ d 5)) (= f (+ g 9))))
(assert (or (= g (+ f 9)) (= g (+ g 11))))

(assert (>= d 0))
(assert (>= e 0))
(assert (>= f 0))
(assert (>= g 0))

(check-sat)