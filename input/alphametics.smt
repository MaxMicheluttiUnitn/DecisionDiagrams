(declare-const V Int)
(declare-const I Int)
(declare-const O Int)
(declare-const L Int)
(declare-const N Int)
(declare-const A Int)
(declare-const T Int)
(declare-const R Int)
(declare-const S Int)

(assert (and (<= V 9) (>= V 0)))
(assert (and (<= I 9) (>= I 0)))
(assert (and (<= O 9) (>= O 0)))
(assert (and (<= L 9) (>= L 0)))
(assert (and (<= N 9) (>= N 0)))
(assert (and (<= A 9) (>= A 0)))
(assert (and (<= T 9) (>= T 0)))
(assert (and (<= R 9) (>= R 0)))
(assert (and (<= S 9) (>= S 0)))

(assert (distinct S O N A T R V I L))

(assert (not (= V 0)))
(assert (not (= S 0)))
(assert (not (= T 0)))

(define-fun VIOLIN () Int (+ (* 100000 V) (* 10000 I) (* 1000 O) (* 100 L) (* 10 I) N))
(define-fun VIOLA () Int (+ (* 10000 V) (* 1000 I) (* 100 O) (* 10 L) A))
(define-fun SONATA () Int (+ (* 100000 S) (* 10000 O) (* 1000 N) (* 100 A) (* 10 T) A))
(define-fun TRIO () Int (+ (* 1000 T) (* 100 R) (* 10 I) O))

(assert (= (+ VIOLIN VIOLIN VIOLA) (+ TRIO SONATA)))

(check-sat)