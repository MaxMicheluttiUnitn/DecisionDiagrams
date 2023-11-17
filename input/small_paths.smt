(declare-const A Int)
(declare-const B Int)
(declare-const C Int)
(declare-const D Int)



; A --3-- B
; |       |
; 5      11
; |       | 
; C --9-- D

(assert (or (= C (+ D 9)) (= C (+ A 5))))
(assert (or (= B (+ D 11)) (= B (+ A 3))))
(assert (or (= A (+ C 5)) (= A (+ B 3))))

(assert (>= D 0))
(assert (= D 0))
(assert (>= B 0))
(assert (>= C 0))
(assert (>= A 0))

(check-sat)