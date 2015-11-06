----------------------------- MODULE TSnapShot -----------------------------
(****************************************************************************
This spec describes an algorithm by Afek et al. described in

   https://en.wikipedia.org/wiki/Shared_snapshot_objects
   
This is the unbounded memory algorithm described there.

This implementation satisfies the TSnapSpec spec, with internal
variables hidden.  
****************************************************************************)
EXTENDS Integers, TLC

CONSTANTS Reader, Writer

ASSUME Reader \cap Writer = { }

Process == Reader \cup Writer
(***************************************************************************)
(* To make it easier to modify the spec to one in which processes write    *)
(* values in some arbitrary set, we write `Value' instead of `Nat'.        *)
(***************************************************************************)
Value == Nat
Memory == [Writer -> Value]
InitMemory == [w \in Writer |-> 0]
NotAMemory ==  [w \in Writer |-> -1]

VARIABLES 
  rstate,  wstate,  \* These variables are the same as in TSnapSpec, since
                    \* they describe the externally visible state.
  rwstate,          \* Like rstate, except has a copy for the writer's state
                    \* of reading as well
  mem, iwriter,     \* The same as in TSnapSpec
  snap,             \* snap[w] is the last snapshot value obtained by
                    \* writer w during its read. 
  \* The following are arrays indexed by Reader \cup Writer, since
  \* both readers and writers perform a read operation.
  rd1, rd2,         \* Two arrays of arrays holding the values obtained in 
                    \* the two reads.
  (*view1,*) view2, \* Two arrays of arrays holding the snap obtained in 
                    \* the second reads.
  notRd1, notRd2,   \* Two arrays holding the sets of writers whose values
                    \* haven't yet been read by each of the reads.
  moved             \* moved[r][w] is the number of times different
                    \* values of mem[w] have been read by r during its
                    \* current read operation.
 
vars ==  <<rstate, wstate, rwstate, mem, iwriter, rd1, rd2, 
           (*view1,*) view2, notRd1, notRd2, moved, snap>>
            
TypeOK == (* /\ rstate  \in [Reader -> Memory \cup {NotAMemory}]
          /\ wstate  \in [Writer -> {"idle", "busy"}]
          /\ rwstate \in [Process -> Memory \cup {NotAMemory}]
          /\ mem     \in Memory
          /\ iwriter \in [Writer -> Nat]
          /\ snap    \in [Writer -> Memory]
          /\ rd1     \in [Process -> Memory]
          /\ rd2     \in [Process -> Memory] *)
\*          /\ view1   \in [Process -> [Writer -> Memory]]
          /\ view2   \in [Process -> [Writer -> Memory]]
(*          /\ notRd1  \in [Process -> SUBSET Writer]
          /\ notRd2  \in [Process -> SUBSET Writer]
          /\ moved   \in [Process -> [Writer -> BOOLEAN]] *)
TypeOK2 == view2   \in [Process -> [Writer -> Memory]]
Init == /\ rstate  = [r \in Reader |-> InitMemory]
        /\ rwstate = [r \in Process |-> InitMemory]
        /\ wstate  = [r \in Writer |-> "idle"]
        /\ mem     = InitMemory
        /\ iwriter = [r \in Writer |-> 0]
        /\ rd1     = [r \in Process |-> InitMemory]
        /\ rd2     = [r \in Process |-> InitMemory]
\*        /\ view1   = [r \in Process |-> [w \in Writer |-> Memory]]
        /\ view2   = [r \in Process |-> [w \in Writer |-> InitMemory]]
        /\ notRd1  = [r \in Process |-> Writer]
        /\ notRd2  = [r \in Process |-> Writer]
        /\ moved   = [r \in Process |-> [w \in Writer |-> FALSE]]
        /\ snap    = [r \in Writer |-> InitMemory]

TypeOK3 == PrintT(TypeOK2)
(***************************************************************************)
(* Define Assign(array, idx, val) to essentially mean                      *)
(*                                                                         *)
(*   array[idx] := val                                                     *)
(*                                                                         *)
(* so the reader of the spec doesn't have to deal with EXCEPT.             *)
(***************************************************************************)
Assign(array, idx, val) == array' = [array EXCEPT ![idx] = val]

(***************************************************************************)
(* Define Assign(array, idx1, idx2, val) to essentially mean               *)
(*                                                                         *)
(*   array[idx1][idx2] := val                                              *)
(*                                                                         *)
(* so the reader of the spec doesn't have to deal with EXCEPT.             *)
(***************************************************************************)
AAssign(array, idx1, idx2, val) == array' = [array EXCEPT ![idx1][idx2] = val]

 
BeginRead(r) == /\ rstate[r] # NotAMemory
                /\ Assign(rstate, r, NotAMemory)
                /\ Assign(rwstate, r, NotAMemory)
                /\ UNCHANGED <<wstate, mem, iwriter, rd1, rd2, 
                               view2, notRd1, notRd2, moved, snap>>
                    
\*vars ==  <<rstate, wstate, rwstate, mem, iwriter, rd1, rd2, 
\*           (*view1,*) view2, notRd1, notRd2, moved, snap>>
DoRd1(r) == /\ rwstate[r] = NotAMemory
            /\ \E w \in notRd1[r] : /\ Assign(notRd1, r, notRd1[r] \ {w})
                                    /\ AAssign(rd1, r, w, mem[w])
\*                                    /\ AAssign(view1, r, w, scan[w])
            /\ UNCHANGED <<rstate, rwstate, wstate, mem, iwriter, rd2, view2, notRd2,
                           moved, snap>>
            
DoRd2(r) == /\ (rwstate[r] = NotAMemory) /\ (notRd1[r] = {})
            /\ \E w \in notRd2[r] : /\ Assign(notRd2, r, notRd2[r] \ {w})
                                    /\ AAssign(rd2, r, w, mem[w])
                                    /\ AAssign(view2, r, w, snap[w])
            /\ UNCHANGED <<rstate, rwstate, wstate, mem, iwriter, rd1, notRd1,
                           moved, snap>>

TryEnding(r) == /\ (rwstate[r] = NotAMemory) /\ (notRd1[r] = {})
                /\ IF rd1[r] = rd2[r] 
                     THEN Assign(rwstate, r, rd1[r]) 
                     ELSE LET F(w) == /\ rd1[r][w] # rd2[r][w]
                                      /\ moved[r][w]
                          IN  IF \E w \in Writer : F(w)
                                THEN Assign(rwstate,r, 
                                            view2[CHOOSE w \in Writer : F(w)])
                                ELSE /\ UNCHANGED rwstate
                                     /\ moved[r] = [w \in Writer |-> 
                                                     moved[r] \/ (rd1[r][w] # rd2[r][w])]
                /\ IF r \in Reader
                     THEN Assign(rstate, r, rwstate'[r])
                     ELSE UNCHANGED rstate
                /\ Assign(moved, r, [w \in Writer |-> FALSE])            
                /\ Assign(notRd1, r, Writer)  
                /\ Assign(notRd2, r, Writer)    
                /\ Assign(rd1, r, InitMemory)   \* To reduce state space
                /\ Assign(rd2, r, InitMemory)   \* To reduce state space
                /\ Assign(view2, r, InitMemory) \* To reduce state space     
                /\ UNCHANGED <<wstate, mem, snap, iwriter>>


BeginWrite(w) == /\ wstate[w] = "idle"
                 /\ Assign(wstate, w, "busy")
                 /\ Assign(iwriter, w, iwriter[w] + 1)
                 /\ Assign(rwstate, w, NotAMemory)
                 /\ UNCHANGED <<rstate, mem, rd1, rd2, view2, notRd1, notRd2, moved, snap>>
                 
DoWrite(w) == /\ iwriter[w] # mem[w]
              /\ rwstate[w] # NotAMemory
              /\ Assign(mem, w, mem[w]+1)
              /\ Assign(snap, w, rwstate[w])
              /\ UNCHANGED <<rstate, wstate, iwriter, rd1, rd2, view2, notRd1, 
                             notRd2, moved>>
              
EndWrite(w) == /\ wstate[w] = "busy"
               /\ Assign(wstate, w, "idle")
               /\ UNCHANGED <<rstate, rwstate, mem, snap, iwriter, rd1, rd2, 
                              view2, notRd1, notRd2, moved>>

Next == \/ \E w \in Writer : BeginWrite(w) \/ DoWrite(w) \/ EndWrite(w)
        \/ \E r \in Reader : 
              BeginRead(r) \/ DoRd1(r) \/ DoRd2(r) \/ TryEnding(r)

Spec == Init /\ [][Next]_vars                     
=============================================================================
\* Modification History
\* Last modified Mon Nov 02 18:16:48 PST 2015 by lamport
\* Created Mon Nov 02 13:33:53 PST 2015 by lamport
