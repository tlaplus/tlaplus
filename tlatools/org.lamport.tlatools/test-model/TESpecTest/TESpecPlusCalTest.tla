---------- MODULE TESpecPlusCalTest -----------

EXTENDS Naturals, TLC

(* --algorithm Steps
variables x = 1, y = FALSE;
begin
    while TRUE do
        x := x + 1;
        y := ~y;
        assert x < 5;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2f1a7a64" /\ chksum(tla) = "93b619e3")
VARIABLES x, y

vars == << x, y >>

Init == (* Global variables *)
        /\ x = 1
        /\ y = FALSE

Next == /\ x' = x + 1
        /\ y' = ~y
        /\ Assert(x' < 5, "Failure of assertion at line 11, column 9.")

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

==============================================
