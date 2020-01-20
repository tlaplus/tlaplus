------------------------------ MODULE CallReturn1 --------------------------- 
EXTENDS Sequences, Naturals, TLC

(********
--algorithm CallReturn1
    procedure Proc1(arg1)
      variable u ;
      begin p1 : u := 2 ;
                 call Proc2 ( 2 * u ) ;
            p2 : assert u = 2;
                 assert arg1  = 4  ;
                 call Proc2 ( 2 * u + 1 ) ;
                 return ;
      end procedure
    procedure Proc2(arg2 = 0)
      variable v = 42 ;
      begin q1 : assert v = 42;
                 assert arg2 \in {4, 5} ;
                 call Proc3 ( v + arg2 ) ;
                 return ;
      end procedure
    procedure Proc3(arg3 = 0)
      begin r1 : assert arg3 \in {46, 47} ;
                 return ;
      end procedure
    begin
      a1 : call Proc1( 4 ) ;
    end algorithm
*****)
  
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3e53299518ce546a0089212b525c3663
CONSTANT defaultInitValue
VARIABLES pc, stack, arg1, u, arg2, v, arg3

vars == << pc, stack, arg1, u, arg2, v, arg3 >>

Init == (* Procedure Proc1 *)
        /\ arg1 = defaultInitValue
        /\ u = defaultInitValue
        (* Procedure Proc2 *)
        /\ arg2 = 0
        /\ v = 42
        (* Procedure Proc3 *)
        /\ arg3 = 0
        /\ stack = << >>
        /\ pc = "a1"

p1 == /\ pc = "p1"
      /\ u' = 2
      /\ /\ arg2' = 2 * u'
         /\ stack' = << [ procedure |->  "Proc2",
                          pc        |->  "p2",
                          v         |->  v,
                          arg2      |->  arg2 ] >>
                      \o stack
      /\ v' = 42
      /\ pc' = "q1"
      /\ UNCHANGED << arg1, arg3 >>

p2 == /\ pc = "p2"
      /\ Assert(u = 2, "Failure of assertion at line 10, column 18.")
      /\ Assert(arg1  = 4, "Failure of assertion at line 11, column 18.")
      /\ /\ arg2' = 2 * u + 1
         /\ stack' = << [ procedure |->  "Proc2",
                          pc        |->  Head(stack).pc,
                          v         |->  v,
                          arg2      |->  arg2 ] >>
                      \o Tail(stack)
         /\ u' = Head(stack).u
      /\ v' = 42
      /\ pc' = "q1"
      /\ UNCHANGED << arg1, arg3 >>

Proc1 == p1 \/ p2

q1 == /\ pc = "q1"
      /\ Assert(v = 42, "Failure of assertion at line 17, column 18.")
      /\ Assert(arg2 \in {4, 5}, 
                "Failure of assertion at line 18, column 18.")
      /\ /\ arg3' = v + arg2
         /\ stack' = << [ procedure |->  "Proc3",
                          pc        |->  Head(stack).pc,
                          arg3      |->  arg3 ] >>
                      \o Tail(stack)
         /\ v' = Head(stack).v
      /\ pc' = "r1"
      /\ UNCHANGED << arg1, u, arg2 >>

Proc2 == q1

r1 == /\ pc = "r1"
      /\ Assert(arg3 \in {46, 47}, 
                "Failure of assertion at line 23, column 18.")
      /\ pc' = Head(stack).pc
      /\ arg3' = Head(stack).arg3
      /\ stack' = Tail(stack)
      /\ UNCHANGED << arg1, u, arg2, v >>

Proc3 == r1

a1 == /\ pc = "a1"
      /\ /\ arg1' = 4
         /\ stack' = << [ procedure |->  "Proc1",
                          pc        |->  "Done",
                          u         |->  u,
                          arg1      |->  arg1 ] >>
                      \o stack
      /\ u' = defaultInitValue
      /\ pc' = "p1"
      /\ UNCHANGED << arg2, v, arg3 >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Proc1 \/ Proc2 \/ Proc3 \/ a1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-21e32d8e366d103d73444c2307bf4aba

                                        
=============================================================================
