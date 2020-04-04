--------------- MODULE etest8  -------------

(* Test that simulation mode doesn't check for deadlock. *)

EXTENDS TLC


VARIABLE x

Init == /\ x \in {"a", "b"}
        /\ Print("This spec can deadlock, but shouldn't.", TRUE)

Next == \/ /\ x = "b"
           /\ x' = "c"
        \/ /\ x = "c"
           /\ x' = "d"
        \/ /\ x = "d"
           /\ x' = "d"
           /\ Assert(FALSE, "Test successfully completed.")

=========================================
