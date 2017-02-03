
(set-option :produce-models true)

; this lets us quantify over
; the set of fields we are reasoning
; about perhaps more conveniently
;
; ie
; (declare-fun marktype (FIELD) MARKTYPE )
; will give the mark assignment to all the fields
; 
; this lets us do things without explicitly making arrays
; and lots of variables with hand-made names potentially
; 
; and lets us have generic code handling multiple variables
; without having to declare all the names manually
; eg field_n1_marktype as a const and look for values for it
;
(declare-datatypes () ((FIELD 
   N1 N2
)))

(declare-datatypes () ((MARKTYPE 
   POINT BAR LINE AREA RULE SYMBOL TEXT TICK
)))

(declare-fun marktype (FIELD) MARKTYPE )

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


; random test
;(declare-const x MARKTYPE)
;(declare-const y MARKTYPE)
;(assert (distinct x y))
;(check-sat)
;(get-model)


; no field should have the same channel
; might be a better way to encode this
(assert (forall ((f1 FIELD) (f2 FIELD)) 
  (implies (not (= f1 f2)) 
    (not (= (channel f1) (channel f2))))))

(check-sat)
; however, it is a bit hard to read-off the solutions this way
; see the model is a bit complicated
; but there may be a way to simplify it
; i’m pretty sure there is a way to get the model back with the functions “labeled” with
; the names we gave them
; AND maybe some way to simplify them 
;
; maybe we can ask Alan about this
(get-model)
(get-value ((channel N1)))
