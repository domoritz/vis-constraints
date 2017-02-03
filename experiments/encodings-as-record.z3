; data types

(declare-datatypes () ((RawType 
   String Number Integer Date
)))

(declare-datatypes () ((Field 
    (mk-field (name String) (type RawType))
)))

; visualization types

(declare-datatypes () ((Marktype 
   Point Bar Line Area Symbol Text Tick
)))

(declare-datatypes () ((Channel 
   X Y Color Size Shape Text Detail
)))

(declare-datatypes () ((FieldType 
   Q O N
)))

(declare-datatypes () ((AggFunc 
   None Count Mean Median Min Max
)))

(declare-datatypes () ((Encoding
    (mk-enc (channel Channel) (field String) (type FieldType) (agg AggFunc))
)))

(define-sort Set (T) (Array T Bool))

(declare-const mark Marktype)
(declare-const encodings (Set Encoding))

; (assert (is-mk-enc2 e1))

; visualization constraints

; wrong: we are not reasoning about instances
(assert (=> (= mark Bar) (exists ((e Encoding)) (= (channel e) X))))
(assert (=> (= mark Bar) (exists ((e Encoding)) (= (channel e) Y))))

; better do something like this where we enumerate the constants
; (assert (=> (= mark Bar) (or (= (channel e1) X) (= (channel e1) Y) (= (channel e2) X) (= (channel e2) Y)) )

; specify partial program

(assert (= mark Bar))

; get output
(check-sat)
(get-model)

(get-value (mark))
