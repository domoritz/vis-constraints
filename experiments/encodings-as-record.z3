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
    (mk-enc (channel Channel) (type FieldType) (agg AggFunc))
)))

; I'm trying to write a function to get the channel from an encoding
;(define-fun channel (e Encoding) Channel
;)

(define-sort Set (T) (Array T Bool))

(declare-const mark Marktype)
(declare-const encodings (Set Encoding))

;(assert (exists ((e Encoding) (= (channel e) X))))

(check-sat)
(get-model)
