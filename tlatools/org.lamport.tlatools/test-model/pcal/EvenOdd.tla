--algorithm EvenOdd
variable result = FALSE;
procedure Even (xEven = 0)
begin
  Even1: if xEven = 0 then
           result := TRUE;
           return;
         else
           call Odd(xEven - 1);
           return;
         end if;
  end procedure
procedure Odd (xOdd = 0)
begin
  Odd1: if xOdd = 0 then result := FALSE;
        else call Even(xOdd - 1);
        end if;
  Odd2: return;
  end procedure
begin
  a1: call Even(N);
  a2: print result;
end algorithm

--------------- MODULE EvenOdd ---------------

EXTENDS Naturals, Sequences, TLC

CONSTANT N

----------------------------------------------


\* BEGIN TRANSLATION (chksum(pcal) = "c9b7b3f7" /\ chksum(tla) = "76b647d3")
VARIABLES pc, result, stack, xEven, xOdd

vars == << pc, result, stack, xEven, xOdd >>

Init == (* Global variables *)
        /\ result = FALSE
        (* Procedure Even *)
        /\ xEven = 0
        (* Procedure Odd *)
        /\ xOdd = 0
        /\ stack = << >>
        /\ pc = "a1"

Even1 == /\ pc = "Even1"
         /\ IF xEven = 0
               THEN /\ result' = TRUE
                    /\ pc' = Head(stack).pc
                    /\ xEven' = Head(stack).xEven
                    /\ stack' = Tail(stack)
                    /\ xOdd' = xOdd
               ELSE /\ /\ stack' = << [ procedure |->  "Odd",
                                        pc        |->  Head(stack).pc,
                                        xOdd      |->  xOdd ] >>
                                    \o Tail(stack)
                       /\ xOdd' = xEven - 1
                    /\ pc' = "Odd1"
                    /\ UNCHANGED << result, xEven >>

Even == Even1

Odd1 == /\ pc = "Odd1"
        /\ IF xOdd = 0
              THEN /\ result' = FALSE
                   /\ pc' = "Odd2"
                   /\ UNCHANGED << stack, xEven >>
              ELSE /\ /\ stack' = << [ procedure |->  "Even",
                                       pc        |->  "Odd2",
                                       xEven     |->  xEven ] >>
                                   \o stack
                      /\ xEven' = xOdd - 1
                   /\ pc' = "Even1"
                   /\ UNCHANGED result
        /\ xOdd' = xOdd

Odd2 == /\ pc = "Odd2"
        /\ pc' = Head(stack).pc
        /\ xOdd' = Head(stack).xOdd
        /\ stack' = Tail(stack)
        /\ UNCHANGED << result, xEven >>

Odd == Odd1 \/ Odd2

a1 == /\ pc = "a1"
      /\ /\ stack' = << [ procedure |->  "Even",
                          pc        |->  "a2",
                          xEven     |->  xEven ] >>
                      \o stack
         /\ xEven' = N
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

\* END TRANSLATION

==============================================


