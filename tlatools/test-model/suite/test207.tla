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
  <2>1. \A K : TRUE
  <2>2. SUFFICES ASSUME NEW L
                 PROVE  TRUE
  <2>3. QED
<1>3a. DEFINE L == 0
<1>4.  K = 0      \* 12 June 14 Changed from <*>4 which is now illegal.
  <2>1. DEFINE F == 7
  <2>4. TRUE   \* 12 June 14 Changed from <*>4 which is now illegal.
  <2>2. QED
     BY <2>4
<1>4a. DEFINE F == 42
<1>5 QED
  BY <1>4
J == 0
I == 0
F == 1

ASSUME PrintT("SANY2 Test")

=============================
