(declare-fun x () Real)
(declare-fun y () Real)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)

(declare-const bad Int)

(define-fun b1 () Bool (< x (- y 1)))
(define-fun b2 () Bool (< (+ y 1) x))
(define-fun a1 () Bool (< 20 x))

(define-fun phi () Bool (and (or b1 b2) (or (not b1) a1)))

(define-fun psi () Bool (and (or (= a (+ b 4)) (= a (+ d 2))) (= c (+ b 4)) (= d (+ a 2))))

(assert (or phi (and (> bad 10) (< bad 5) psi)))

(assert (>= a 0))
(assert (= b 0))
(assert (>= c 0))
(assert (>= d 0))

(check-sat)