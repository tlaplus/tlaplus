---------------------------- MODULE test38 -----------------------------

(* Test of EXTENDS *)

EXTENDS test38a, TLC

VARIABLES x
\* CONSTANT c

Init == MInit(x)
Next == x'=c
Inv  == IF (x=c) THEN Print("Test OK", TRUE)
                 ELSE Print("Test Failed", TRUE)


=============================================================================
