------------------------------- MODULE Either3 ------------------------------ 
EXTENDS Naturals, Sequences, TLC

(* --algorithm Either
      variables x = 0 ; y = 0 ; z = 0 ;
      begin a: either    x := 1 ; 
                      b: x := x + 1; 
                   or y := 1 ; c: y := y + 1;
                   or z := 100
               end either ;
            d: either when x = 0 ; z := z + 1 ;
                   or when x = 2 ; z := z + 3 ;
               end either ;     
               assert (x+y = 2) \/ ((z = 101) /\ (x+y=0));
               assert (z < 100) => (z = x + 1) ;
     end algorithm
*)

\* BEGIN TRANSLATION PC-00b333ef55d000b1adf10ced24b787d0dc5f99e2929dfb9a8445fc0c9622be20
VARIABLES x, y, z, pc

vars == << x, y, z, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ z = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ \/ /\ x' = 1
           /\ pc' = "b"
           /\ UNCHANGED <<y, z>>
        \/ /\ y' = 1
           /\ pc' = "c"
           /\ UNCHANGED <<x, z>>
        \/ /\ z' = 100
           /\ pc' = "d"
           /\ UNCHANGED <<x, y>>

b == /\ pc = "b"
     /\ x' = x + 1
     /\ pc' = "d"
     /\ UNCHANGED << y, z >>

c == /\ pc = "c"
     /\ y' = y + 1
     /\ pc' = "d"
     /\ UNCHANGED << x, z >>

d == /\ pc = "d"
     /\ \/ /\ x = 0
           /\ z' = z + 1
        \/ /\ x = 2
           /\ z' = z + 3
     /\ Assert((x+y = 2) \/ ((z' = 101) /\ (x+y=0)), 
               "Failure of assertion at line 14, column 16.")
     /\ Assert((z' < 100) => (z' = x + 1), 
               "Failure of assertion at line 15, column 16.")
     /\ pc' = "Done"
     /\ UNCHANGED << x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ c \/ d
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION TPC-80f4b4b1d438c72bd2c0d24645f017d91f658078b981a0d1d842959c4897e104

=============================================================================
