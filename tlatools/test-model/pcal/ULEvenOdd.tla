--algorithm EvenOdd
variable result = FALSE;
procedure Even (xEven = 0)
begin
  (*Even1:*) if xEven = 0 then
           result := TRUE;
           return;
         else
           call Odd(xEven - 1);
           return;
         end if;
  end procedure
procedure Odd (xOdd = 0)
begin
  (*Odd1:*) if xOdd = 0 then result := FALSE;
        else call Even(xOdd - 1);
        end if;
  (*Odd2:*) return;
  end procedure
begin
  (*a1:*) call Even(N);
  (*a2:*) print result;
end algorithm

--------------- MODULE ULEvenOdd ---------------

EXTENDS Naturals, Sequences, TLC

CONSTANT N

----------------------------------------------


\* BEGIN TRANSLATION PC-142ef629b4f0aa18a59e2ceb8e2d82f2c6e79a7706b141e97f71050cdbe3fa3a
VARIABLES result, pc, stack, xEven, xOdd

vars == << result, pc, stack, xEven, xOdd >>

Init == (* Global variables *)
        /\ result = FALSE
        (* Procedure Even *)
        /\ xEven = 0
        (* Procedure Odd *)
        /\ xOdd = 0
        /\ stack = << >>
        /\ pc = "Lbl_4"

Lbl_1 == /\ pc = "Lbl_1"
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
                    /\ pc' = "Lbl_2"
                    /\ UNCHANGED << result, xEven >>

Even == Lbl_1

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF xOdd = 0
               THEN /\ result' = FALSE
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << stack, xEven >>
               ELSE /\ /\ stack' = << [ procedure |->  "Even",
                                        pc        |->  "Lbl_3",
                                        xEven     |->  xEven ] >>
                                    \o stack
                       /\ xEven' = xOdd - 1
                    /\ pc' = "Lbl_1"
                    /\ UNCHANGED result
         /\ xOdd' = xOdd

Lbl_3 == /\ pc = "Lbl_3"
         /\ pc' = Head(stack).pc
         /\ xOdd' = Head(stack).xOdd
         /\ stack' = Tail(stack)
         /\ UNCHANGED << result, xEven >>

Odd == Lbl_2 \/ Lbl_3

Lbl_4 == /\ pc = "Lbl_4"
         /\ /\ stack' = << [ procedure |->  "Even",
                             pc        |->  "Lbl_5",
                             xEven     |->  xEven ] >>
                         \o stack
            /\ xEven' = N
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << result, xOdd >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ PrintT(result)
         /\ pc' = "Done"
         /\ UNCHANGED << result, stack, xEven, xOdd >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Even \/ Odd \/ Lbl_4 \/ Lbl_5
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION TPC-bd56803e88aa64534c5647dd25fd802290c4fc72a9f2a2cf1f5de901b8982de7

==============================================


