---------------------------- MODULE EvenOddBad -----------------------------

EXTENDS Naturals, Sequences, TLC

(*
--algorithm EvenOddBad
variable result \in { TRUE, FALSE };
procedure Even (xEven = 0)
begin
  Even1: if xEven = 0 then result := TRUE;
         else call Odd(xEven - 1);
         end if;
     e1  :  return;
  end procedure;
procedure Odd (xOdd = 0)
begin
  Odd1: if xOdd = 0 then result := FALSE;
        else call Even(xOdd - 1);
        end if;
      o1 :  return;
  end procedure
begin
  a1: call Even(2);
  a2: print result;
end algorithm
*)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4f4604590279cc4b2920a972bf28fdd0
VARIABLES result, pc, stack, xEven, xOdd

vars == << result, pc, stack, xEven, xOdd >>

Init == (* Global variables *)
        /\ result \in { TRUE, FALSE }
        (* Procedure Even *)
        /\ xEven = 0
        (* Procedure Odd *)
        /\ xOdd = 0
        /\ stack = << >>
        /\ pc = "a1"

Even1 == /\ pc = "Even1"
         /\ IF xEven = 0
               THEN /\ result' = TRUE
                    /\ pc' = "e1"
                    /\ UNCHANGED << stack, xOdd >>
               ELSE /\ /\ stack' = << [ procedure |->  "Odd",
                                        pc        |->  "e1",
                                        xOdd      |->  xOdd ] >>
                                    \o stack
                       /\ xOdd' = xEven - 1
                    /\ pc' = "Odd1"
                    /\ UNCHANGED result
         /\ xEven' = xEven

e1 == /\ pc = "e1"
      /\ pc' = Head(stack).pc
      /\ xEven' = Head(stack).xEven
      /\ stack' = Tail(stack)
      /\ UNCHANGED << result, xOdd >>

Even == Even1 \/ e1

Odd1 == /\ pc = "Odd1"
        /\ IF xOdd = 0
              THEN /\ result' = FALSE
                   /\ pc' = "o1"
                   /\ UNCHANGED << stack, xEven >>
              ELSE /\ /\ stack' = << [ procedure |->  "Even",
                                       pc        |->  "o1",
                                       xEven     |->  xEven ] >>
                                   \o stack
                      /\ xEven' = xOdd - 1
                   /\ pc' = "Even1"
                   /\ UNCHANGED result
        /\ xOdd' = xOdd

o1 == /\ pc = "o1"
      /\ pc' = Head(stack).pc
      /\ xOdd' = Head(stack).xOdd
      /\ stack' = Tail(stack)
      /\ UNCHANGED << result, xEven >>

Odd == Odd1 \/ o1

a1 == /\ pc = "a1"
      /\ /\ stack' = << [ procedure |->  "Even",
                          pc        |->  "a2",
                          xEven     |->  xEven ] >>
                      \o stack
         /\ xEven' = 2
      /\ pc' = "Even1"
      /\ UNCHANGED << result, xOdd >>

a2 == /\ pc = "a2"
      /\ PrintT(result)
      /\ pc' = "Done"
      /\ UNCHANGED << result, stack, xEven, xOdd >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Even \/ Odd \/ a1 \/ a2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-7dc8ff54d82fc57126829898458b6c6f

=============================================================================
