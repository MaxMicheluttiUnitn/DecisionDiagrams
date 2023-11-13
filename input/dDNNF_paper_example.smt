;;b1 = LT(x,Minus(y,Real(1)))
;;b2 = LT(Plus(y,Real(1)),x)
;;a = LT(Real(20),x)
;;phi = And(Or(b1,b2),Or(Not(b1),a))
(declare-fun x () Real)
(declare-fun y () Real)

(define-fun b1 () Bool (< x (- y 1)))
(define-fun b2 () Bool (< (+ y 1) x))
(define-fun a () Bool (< 20 x))

(assert (or b1 b2))
(assert (or (not b1) a))

(check-sat)