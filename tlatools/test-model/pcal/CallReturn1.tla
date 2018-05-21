------------------------------ MODULE CallReturn1 --------------------------- 
EXTENDS Sequences, Naturals, TLC

(*   
  --algorithm CallReturn1
    procedure Proc1(arg1 = 0)
      variable u = 1 ;
      begin p1 : u := 2 ;
                 call Proc2 ( 2 * u ) ;
            p2 : when Print ( << u , " = 2 " >> , TRUE ) ;
                 when Print ( << arg1, " = 4 " >> , TRUE ) ;
                 call Proc2 ( 2 * u + 1 ) ;
                 return ;
      end procedure
    procedure Proc2(arg2 = 0)
      variable v = 42 ;
      begin q1 : when Print( << v , " = 42 " >> , TRUE ) ;
                 when Print ( << arg2, " = 4 then 5 " >> , TRUE ) ;
                 call Proc3 ( v + arg2 ) ;
                 return ;
      end procedure
    procedure Proc3(arg3 = 0)
      begin r1 : when Print( << arg3, " = 46 then 47 " >> , TRUE ) ;
                 return ;
      end procedure
    begin
      a1 : call Proc1( 4 ) ;
    end algorithm

*)
					
(***** BEGIN TRANSLATION ***)
VARIABLES pc, stack, arg1, u, arg2, v, arg3

vars == << pc, stack, arg1, u, arg2, v, arg3 >>

Init == (* Procedure Proc1 *)
        /\ arg1 = 0
        /\ u = 1
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
      /\ Print ( << u , " = 2 " >> , TRUE )
      /\ Print ( << arg1, " = 4 " >> , TRUE )
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
      /\ Print( << v , " = 42 " >> , TRUE )
      /\ Print ( << arg2, " = 4 then 5 " >> , TRUE )
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
      /\ Print( << arg3, " = 46 then 47 " >> , TRUE )
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
      /\ u' = 1
      /\ pc' = "p1"
      /\ UNCHANGED << arg2, v, arg3 >>

Next == Proc1 \/ Proc2 \/ Proc3 \/ a1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

(***** END TRANSLATION ***)
=============================================================================
