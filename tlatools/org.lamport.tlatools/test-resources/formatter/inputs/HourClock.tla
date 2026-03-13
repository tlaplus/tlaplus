This is some text explaining the spec.
Has multiple lines in it.
---------------------- MODULE HourClock ----------------------
EXTENDS Naturals, TLC
VARIABLE hr
HCini  ==  hr \in (1 .. 12)
HCnxt  ==  hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC  ==  HCini /\ [][HCnxt]_hr
--------------------------------------------------------------
THEOREM  HC => []HCini
==============================================================
This is post text
Has multiple lines in it.