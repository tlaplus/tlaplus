--------------------------- MODULE InitEvalOrder ---------------------------
VARIABLE Clk1
S1 == INSTANCE Base  WITH  clk <- Clk1

VARIABLE Clk2
S2 == INSTANCE Base  WITH  clk <- Clk2

Spec1 == 
       /\ S1!Init /\ S2!Init /\ (Clk2 = Clk1)
       /\ [][UNCHANGED <<Clk1, Clk2>>]_<<S1!vars, S2!vars>>

Spec2 == 
       /\ S2!Init /\ S1!Init /\ (Clk1 = Clk2)
       /\ [][UNCHANGED <<Clk1, Clk2>>]_<<S1!vars, S2!vars>>

Spec3 == 
       /\ S1!Init /\ S2!Init /\ (Clk1 = Clk2)
       /\ [][UNCHANGED <<Clk1, Clk2>>]_<<S1!vars, S2!vars>>

Spec4 == 
       /\ S2!Init /\ S1!Init /\ (Clk2 = Clk1)
       /\ [][UNCHANGED <<Clk1, Clk2>>]_<<S1!vars, S2!vars>>
=============================================================================
