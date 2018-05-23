----------------------------- MODULE DetlefTest ----------------------------- 
EXTENDS Detlefs2

qRFrom[adr \in Address] == IF adr = LeftHat 
                THEN  <<Mem[adr].V>>
                ELSE  qRFrom[Mem[adr].R] \o <<Mem[adr].V>>

qBar == IF Mem[RightHat].R = RightHat 
          THEN << >> 
          ELSE qRFrom[RightHat]

rVBar == [p \in Procs |-> 
           CASE 
                pc[p] \in {"M4", "M7"} -> Mem[rh[p]].V
             [] pc[p] = "M8" -> result[p]
             [] pc[p] \in {"O5", "O8"} -> Mem[rh[p]].V
             [] pc[p] = "O9" -> result[p]
             [] OTHER -> rVal[p]]

pcBar == [p \in Procs |-> IF rVBar[p] = null THEN "L1" ELSE "L2"]

SpecBar == INSTANCE DetlefSpec WITH rV <- rVBar, pc <- pcBar,
                                    N <- 100
QSpec == SpecBar!Spec

CONSTANTS a1, a2, a3, a4, v1, v2, p1, p2, p3
XInit == 
/\ lh = (p1 :> a1 @@ p2 :> a1)
/\ LeftHat = a2
/\ nd = (p1 :> a2 @@ p2 :> null)
/\ RightHat = a2
/\ rVal = (p1 :> "okay" @@ p2 :> null)
/\ valBag = (v1 :> 0)
/\ pc = (p1 :> "Return" @@ p2 :> "M2")
/\ temp = (p1 :> TRUE @@ p2 :> a1)
/\ rh = (p1 :> a1 @@ p2 :> a1)
/\ Mem = ( a1 :> [V |-> null, R |-> a1, L |-> a1] @@
  a2 :> [V |-> v1, R |-> a1, L |-> a1] @@
  a3 :> [V |-> null, R |-> null, L |-> null] @@
  a4 :> [V |-> null, R |-> null, L |-> null] )
/\ queue = << v1 >>
/\ ptr = (p1 :> a1 @@ p2 :> a1)
/\ result = (p1 :> v1 @@ p2 :> v1)
/\ freeList = {a3, a4}

XSpec == XInit /\ [][Next]_vars

XQSpec == [][SpecBar!Next]_(SpecBar!vars)
=============================================================================