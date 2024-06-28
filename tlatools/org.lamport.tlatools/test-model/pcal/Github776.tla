------------------------------ MODULE Github776 -----------------------------

EXTENDS Naturals, Sequences, TLC

(*--algorithm Playground {

    \* PlusCal does not have return values, but we can fake them
    variables
        retval,
        output

    procedure add(x, y) {
        do_add:
            retval := x + y;
            return;
    }

    procedure to_string(int) {
        do_to_string:
            assert int = 10; \* this model only needs to be able to convert one value to a string
            retval := "10";
            return;
    }

    fair process (main = 1) {
        step1: call add(3, 7);
        step2: call to_string(retval);
        step3: output := retval;
        step4: assert output = "10";
    }

}*)
\* BEGIN TRANSLATION (chksum(pcal) = "90defa92" /\ chksum(tla) = "375b0aff")
CONSTANT defaultInitValue
VARIABLES pc, retval, output, stack, x, y, int

vars == << pc, retval, output, stack, x, y, int >>

ProcSet == {1}

Init == (* Global variables *)
        /\ retval = defaultInitValue
        /\ output = defaultInitValue
        (* Procedure add *)
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ y = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure to_string *)
        /\ int = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "step1"]

do_add(self) == /\ pc[self] = "do_add"
                /\ retval' = x[self] + y[self]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
                /\ y' = [y EXCEPT ![self] = Head(stack[self]).y]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << output, int >>

add(self) == do_add(self)

do_to_string(self) == /\ pc[self] = "do_to_string"
                      /\ Assert(int[self] = 10, 
                                "Failure of assertion at line 20, column 13.")
                      /\ retval' = "10"
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ int' = [int EXCEPT ![self] = Head(stack[self]).int]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << output, x, y >>

to_string(self) == do_to_string(self)

step1 == /\ pc[1] = "step1"
         /\ /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "add",
                                                  pc        |->  "step2",
                                                  x         |->  x[1],
                                                  y         |->  y[1] ] >>
                                              \o stack[1]]
            /\ x' = [x EXCEPT ![1] = 3]
            /\ y' = [y EXCEPT ![1] = 7]
         /\ pc' = [pc EXCEPT ![1] = "do_add"]
         /\ UNCHANGED << retval, output, int >>

step2 == /\ pc[1] = "step2"
         /\ /\ int' = [int EXCEPT ![1] = retval]
            /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "to_string",
                                                  pc        |->  "step3",
                                                  int       |->  int[1] ] >>
                                              \o stack[1]]
         /\ pc' = [pc EXCEPT ![1] = "do_to_string"]
         /\ UNCHANGED << retval, output, x, y >>

step3 == /\ pc[1] = "step3"
         /\ output' = retval
         /\ pc' = [pc EXCEPT ![1] = "step4"]
         /\ UNCHANGED << retval, stack, x, y, int >>

step4 == /\ pc[1] = "step4"
         /\ Assert(output = "10", 
                   "Failure of assertion at line 29, column 16.")
         /\ pc' = [pc EXCEPT ![1] = "Done"]
         /\ UNCHANGED << retval, output, stack, x, y, int >>

main == step1 \/ step2 \/ step3 \/ step4

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet: add(self) \/ to_string(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(main) /\ WF_vars(add(1)) /\ WF_vars(to_string(1))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


Liveness == []<>(pc[1] = "Done")
=============================================================================

------------ CONFIG Github776 -----------------
SPECIFICATION Spec
CONSTANT defaultInitValue = defaultInitValue
PROPERTY Liveness
=======================================
