--------------------------- MODULE BinaryHourClock --------------------------
EXTENDS Naturals

VARIABLE bits 

H(hr) == INSTANCE HourClock 

BitArrayVal(b) == 
    LET n  ==  CHOOSE i \in Nat : DOMAIN b = 0..i

        val[i \in 0..n]  == 
            IF  i=0  THEN  b[0] * 2^0  ELSE  (b[i] * 2^i) + val[i-1]
    IN val[n] 

HourVal(b) == IF b \in[(0.. 3) -> {0,1}] THEN BitArrayVal(b) 
                                         ELSE 99 
 
IR(b, h) == [](h = HourVal(b))

BHC  ==  \EE hr : IR(bits, hr) /\ H(hr)!HC
=============================================================================
