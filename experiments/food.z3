; declarations
(declare-const fruit Real)
(declare-const fries Real)
(declare-const salad Real)
(declare-const wings Real)

(declare-const total Real)

(declare-const mul1 Int)
(declare-const mul2 Int)
(declare-const mul3 Int)
(declare-const mul4 Int)

; assert variables
(assert (= fruit 2.15))
(assert (= fries 2.75))
(assert (= salad 3.50))
(assert (= wings 3.00))

(assert (= total 12))

; assert that all multiplicators are positive
(assert (>= mul1 0))
(assert (>= mul2 0))
(assert (>= mul3 0))
(assert (>= mul4 0))

; we have to spend exactly the total amount
(assert (= (+ (* mul1 fruit) (* mul2 fries) (* mul3 salad) (* mul4 wings)) total))

; maximize the number of items
(maximize (+ mul1 mul2 mul3 mul4))

(check-sat)

(echo "Number of items we should buy")
(eval mul1)
(eval mul2)
(eval mul3)
(eval mul4)
