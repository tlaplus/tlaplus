--------------------------- MODULE SimpleMultiProc -------------------------- 
EXTENDS Naturals, Sequences, TLC

(*   
--algorithm SimpleMultiProc                                             
     variables                                                           
       x = [i \in ProcSet |-> CASE i = 41 -> 1 []                         
                                   i = 42 -> 2 []                         
                                   i = 43 -> 3 []                         
                                   i = 44 -> 4 []                         
                                   i = 45 -> 5];                          
       sum = 0 ;                                                         
       done = {};
     procedure AddMe(me = 0)
       variable y = 0;
       begin am: done := done \cup { me } ;
                 return ;
       end procedure                                                         
     process ProcA = 41                                                  
       variable y = 0;                                                   
       begin a1 : sum := sum + y + x [ 41 ] ||
                  y := sum ;                           
             a2 : call AddMe(41) ;                             
             a3 : when done = { 41, 42, 43, 44, 45 } ; 
       end process                                                       
     process ProcB \in 42 .. 43                                          
       variable z \in {2, 3} ;                                           
       begin b1 : sum := sum + z + x [ self ] ;                          
             b2 : call AddMe(self);                           
       end process                                                       
     process ProcC \in { 44,
                         45 }                                          
       variable z \in {4, 5} ;                                           
       begin c1 : sum := sum + z + x [ self ] ;                          
             c2 : call AddMe(self) ;                           
       end process                                                       
     end algorithm         

*)
                    
\* BEGIN TRANSLATION
\* Process variable y of process ProcA at line 20 col 17 changed to y_
\* Process variable z of process ProcB at line 27 col 17 changed to z_
VARIABLES x, sum, done, pc, stack, me, y, y_, z_, z

vars == << x, sum, done, pc, stack, me, y, y_, z_, z >>

ProcSet == {41} \cup (42 .. 43) \cup ({ 44,
                                        45 })

Init == (* Global variables *)
        /\ x = [i \in ProcSet |-> CASE i = 41 -> 1 []
                                       i = 42 -> 2 []
                                       i = 43 -> 3 []
                                       i = 44 -> 4 []
                                       i = 45 -> 5]
        /\ sum = 0
        /\ done = {}
        (* Procedure AddMe *)
        /\ me = [ self \in ProcSet |-> 0]
        /\ y = [ self \in ProcSet |-> 0]
        (* Process ProcA *)
        /\ y_ = 0
        (* Process ProcB *)
        /\ z_ \in [42 .. 43 -> {2, 3}]
        (* Process ProcC *)
        /\ z \in [{ 44,
                    45 } -> {4, 5}]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 41 -> "a1"
                                        [] self \in 42 .. 43 -> "b1"
                                        [] self \in { 44,
                                                      45 } -> "c1"]

am(self) == /\ pc[self] = "am"
            /\ done' = (done \cup { me[self] })
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ y' = [y EXCEPT ![self] = Head(stack[self]).y]
            /\ me' = [me EXCEPT ![self] = Head(stack[self]).me]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << x, sum, y_, z_, z >>

AddMe(self) == am(self)

a1 == /\ pc[41] = "a1"
      /\ /\ sum' = sum + y_ + x [ 41 ]
         /\ y_' = sum
      /\ pc' = [pc EXCEPT ![41] = "a2"]
      /\ UNCHANGED << x, done, stack, me, y, z_, z >>

a2 == /\ pc[41] = "a2"
      /\ /\ me' = [me EXCEPT ![41] = 41]
         /\ stack' = [stack EXCEPT ![41] = << [ procedure |->  "AddMe",
                                                pc        |->  "a3",
                                                y         |->  y[41],
                                                me        |->  me[41] ] >>
                                            \o stack[41]]
      /\ y' = [y EXCEPT ![41] = 0]
      /\ pc' = [pc EXCEPT ![41] = "am"]
      /\ UNCHANGED << x, sum, done, y_, z_, z >>

a3 == /\ pc[41] = "a3"
      /\ done = { 41, 42, 43, 44, 45 }
      /\ pc' = [pc EXCEPT ![41] = "Done"]
      /\ UNCHANGED << x, sum, done, stack, me, y, y_, z_, z >>

ProcA == a1 \/ a2 \/ a3

b1(self) == /\ pc[self] = "b1"
            /\ sum' = sum + z_[self] + x [ self ]
            /\ pc' = [pc EXCEPT ![self] = "b2"]
            /\ UNCHANGED << x, done, stack, me, y, y_, z_, z >>

b2(self) == /\ pc[self] = "b2"
            /\ /\ me' = [me EXCEPT ![self] = self]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "AddMe",
                                                        pc        |->  "Done",
                                                        y         |->  y[self],
                                                        me        |->  me[self] ] >>
                                                    \o stack[self]]
            /\ y' = [y EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "am"]
            /\ UNCHANGED << x, sum, done, y_, z_, z >>

ProcB(self) == b1(self) \/ b2(self)

c1(self) == /\ pc[self] = "c1"
            /\ sum' = sum + z[self] + x [ self ]
            /\ pc' = [pc EXCEPT ![self] = "c2"]
            /\ UNCHANGED << x, done, stack, me, y, y_, z_, z >>

c2(self) == /\ pc[self] = "c2"
            /\ /\ me' = [me EXCEPT ![self] = self]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "AddMe",
                                                        pc        |->  "Done",
                                                        y         |->  y[self],
                                                        me        |->  me[self] ] >>
                                                    \o stack[self]]
            /\ y' = [y EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "am"]
            /\ UNCHANGED << x, sum, done, y_, z_, z >>

ProcC(self) == c1(self) \/ c2(self)

Next == ProcA
           \/ (\E self \in ProcSet: AddMe(self))
           \/ (\E self \in 42 .. 43: ProcB(self))
           \/ (\E self \in { 44,
                             45 }: ProcC(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ProcA) /\ WF_vars(AddMe(41))
        /\ \A self \in 42 .. 43 : WF_vars(ProcB(self)) /\ WF_vars(AddMe(self))
        /\ \A self \in { 44,
                         45 } : WF_vars(ProcC(self)) /\ WF_vars(AddMe(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
