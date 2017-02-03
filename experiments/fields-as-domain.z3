
(set-option :produce-models true)

; this lets us quantify over
; the set of fields we are reasoning about 
(declare-datatypes () ((FIELD 
   Mpg Horsepower
)))

(declare-datatypes () ((MARKTYPE 
   POINT BAR LINE AREA RULE SYMBOL TEXT TICK
)))

; (declare-fun marktype (FIELD) MARKTYPE )
; will give the mark assignment to all the fields
; 
; this lets us do things without 
; lots of variables with hand-made names potentially
(declare-fun marktype (FIELD) MARKTYPE )


; Declarations and Assignment Functions
; For other types

(declare-datatypes () ((CHANNEL 
   X Y COLOR SIZE SHAPE TEXT DETAIL
)))

(declare-fun channel (FIELD) CHANNEL )

(declare-datatypes () ((FIELD_TYPE 
   Q O N
)))

(declare-fun ftype (FIELD) FIELD_TYPE )

(declare-datatypes () ((AGG_FUNC 
   COUNT MEAN MEDIAN MIN MAX
)))



; and lets us have generic code for domain constraints

; no field should have the same channel
(assert (forall ((f1 FIELD) (f2 FIELD)) 
  (implies (not (= f1 f2)) 
    (not (= (channel f1) (channel f2))))))

(check-sat)

; however, it is a bit hard to read-off the solutions this way
; so have to generate the read-off model code
; but it is at least independent
; from expression of the domain constraints

(get-model)
(get-value ((channel Mpg) (channel Horsepower)))
