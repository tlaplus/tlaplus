------------------------------- MODULE RAB -------------------------------

EXTENDS Naturals, Sequences, TLC


(**************************************************************************)
(* The Remoting Attributes bug.                                           *)
(*                                                                        *)
(*                                                                        *)
(* Simplified version of the c program (comment in the original):         *)
(*                                                                        *)
(*                                                                        *)
(*    class Attributes {                                                  *)
(*        int flags = 0;                                                  *)
(*                                                                        *)
(*        boolean CalcA () { ... }                                        *)
(*        boolean CalcB () { ... }                                        *)
(*                                                                        *)
(*        // We are not protecting against a race.                        *)
(*        // If there is a race while setting flags we                    *)
(*        // will have to compute the result again, but                   *)
(*        // we will always return the correct result.                    *)
(*                                                                        *)
(*        boolean isA () {                                                *)
(*            if ((flags & 0x02) == 0) {                                  *)
(*                int temp = (CalcA() ? 0x03 : 0x02);                     *)
(*                flags |= temp;                                          *)
(*            }                                                           *)
(*            return (flags & 0x01) != 0;                                 *)
(*        }                                                               *)
(*                                                                        *)
(*        boolean isB () {                                                *)
(*            if ((flags & 0x20) == 0) {                                  *)
(*                int temp = (CalcB() ? 0x30 : 0x20);                     *)
(*                flags |= temp;                                          *)
(*            }                                                           *)
(*            return (flags & 0x10) != 0;                                 *)
(*        }                                                               *)
(*    }                                                                   *)
(*                                                                        *)
(*                                                                        *)
(* CalcA and CalcB are assumed to be functions that each always returns   *)
(* the same value; we just do not know what value that is.  We model this *)
(* using an "oracle" global variable named calc.                          *)
(*                                                                        *)
(* We model the environment as a set of processes Pid.  Each process runs *)
(* in a loop, selecting a random attribute ("A" or "B") to access on each *)
(* iteration.                                                             *)
(*                                                                        *)
(**************************************************************************)

CONSTANT Pid        \* set of process ids

Attr == { "A", "B" }         \* what are the attributes
Boolean == { FALSE, TRUE }

Flags == [ Attr -> [ valid: Boolean, value: Boolean ]]



(**************************************************************************)
(* How to compute the "bitwise or" of two Flags.                          *)
(**************************************************************************)
f | g == [ a \in DOMAIN f |-> [ n \in DOMAIN f[a] |-> f[a][n] \/ g[a][n] ]]







(*--algorithm rab

    variables
        (****************************************************************)
        (* Global variable containing flags for all attributes.   The   *)
        (* initial state has all valid and value bits as FALSE.         *)
        (****************************************************************)
        flags = [ a \in Attr |-> [ valid |-> FALSE, value |-> FALSE ]];


        (****************************************************************)
        (* Oracle that says what the value is for each attribute.       *)
        (* Technically this is a variable, but we never change it.      *)
        (****************************************************************)
        calc \in [ Attr -> { FALSE, TRUE } ];




    process work \in Pid
        variables
            (************************************************************)
            (* Arbitrary initial values of the correct type.            *)
            (************************************************************)
            temp = CHOOSE f \in Flags : TRUE;
            myattr = CHOOSE a \in Attr : TRUE;
    begin
      Loop:
        while TRUE do
            (************************************************************)
            (* Choose an attribute to access.                           *)
            (************************************************************)
            with attr \in Attr do myattr := attr; end with;

            if \lnot flags[myattr].valid then
                (********************************************************)
                (* My component of the global flags variable is not     *)
                (* valid.   Compute the temporary.                      *)
                (********************************************************)
                temp :=
                [ a \in Attr |->
                    IF a = myattr
                    THEN [ valid |-> TRUE, value |-> calc[myattr] ]
                    ELSE [ valid |-> FALSE, value |-> FALSE ]
                ];

              FetchFlags:
                (********************************************************)
                (* Fetch the global flags variable and "bitwise or" it  *)
                (* into the temporary.                                  *)
                (********************************************************)
                temp := flags | temp;

              StoreFlags:
                (********************************************************)
                (* Store the temporary back into the global flags       *)
                (* variable.                                            *)
                (********************************************************)
    
                flags := temp;
            end if;

          ReadFlags:
            (************************************************************)
            (* Read my component of the global flags variable.  It is   *)
            (* supposed to be consistent with the oracle.               *)
            (************************************************************)
            \* assert flags[myattr].value = calc[myattr];
            skip;
        end while;
    end process;
end algorithm

*)    


\* BEGIN TRANSLATION (chksum(pcal) = "da7526ed" /\ chksum(tla) = "4913b402")
VARIABLES pc, flags, calc, temp, myattr

vars == << pc, flags, calc, temp, myattr >>

ProcSet == (Pid)

Init == (* Global variables *)
        /\ flags = [ a \in Attr |-> [ valid |-> FALSE, value |-> FALSE ]]
        /\ calc \in [ Attr -> { FALSE, TRUE } ]
        (* Process work *)
        /\ temp = [self \in Pid |-> CHOOSE f \in Flags : TRUE]
        /\ myattr = [self \in Pid |-> CHOOSE a \in Attr : TRUE]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ \E attr \in Attr:
                   myattr' = [myattr EXCEPT ![self] = attr]
              /\ IF \lnot flags[myattr'[self]].valid
                    THEN /\ temp' = [temp EXCEPT ![self] = [ a \in Attr |->
                                                               IF a = myattr'[self]
                                                               THEN [ valid |-> TRUE, value |-> calc[myattr'[self]] ]
                                                               ELSE [ valid |-> FALSE, value |-> FALSE ]
                                                           ]]
                         /\ pc' = [pc EXCEPT ![self] = "FetchFlags"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ReadFlags"]
                         /\ temp' = temp
              /\ UNCHANGED << flags, calc >>

ReadFlags(self) == /\ pc[self] = "ReadFlags"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Loop"]
                   /\ UNCHANGED << flags, calc, temp, myattr >>

FetchFlags(self) == /\ pc[self] = "FetchFlags"
                    /\ temp' = [temp EXCEPT ![self] = flags | temp[self]]
                    /\ pc' = [pc EXCEPT ![self] = "StoreFlags"]
                    /\ UNCHANGED << flags, calc, myattr >>

StoreFlags(self) == /\ pc[self] = "StoreFlags"
                    /\ flags' = temp[self]
                    /\ pc' = [pc EXCEPT ![self] = "ReadFlags"]
                    /\ UNCHANGED << calc, temp, myattr >>

work(self) == Loop(self) \/ ReadFlags(self) \/ FetchFlags(self)
                 \/ StoreFlags(self)

Next == (\E self \in Pid: work(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


Consistency ==
    \A self \in ProcSet :
    pc[self] = "ReadFlags" =>
        flags[myattr[self]].value = calc[myattr[self]]


============================================================================
