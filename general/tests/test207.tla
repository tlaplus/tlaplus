\* SANY2 test.
\* Test of scope of NEW declarations.  They should be restricted
\* to the statement's proof, except for SUFFICES which should be 
\* visible to the rest of the current proof.

-------------------- MODULE test207 ----------------
EXTENDS TLC
a + b == <<a, b>>
THEOREM Thm == ASSUME NEW J PROVE lab :: TRUE
<1>1 ASSUME NEW I
     PROVE  Thm!lab
  <2>1 I = J
  <2>2 QED
<1> DEFINE I == 1
<1>2 ASSUME NEW K
     PROVE  TRUE
<1>3 SUFFICES ASSUME NEW K
              PROVE  TRUE
<1>4 K = 0
<1>5 QED

J == 0

ASSUME PrintT("SANY2 Test")

=============================
