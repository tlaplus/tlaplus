                
--algorithm bug
variables x = 0 ; y = 0 ;
macro foo()
   begin if TRUE then if TRUE then y := 22 ;
                              else y := 42  end if
                 else  with a = 47 ; b = 77 ; do
                        y := 27
                       end with  end if
   end macro 
procedure Bar() 
  begin Q: skip ;
           foo() ;
           return 
  end procedure 
begin  L1 :   y := 1 ;
       L3 :   skip ;
              if x > 0 then foo() 
                       else x := 17 end if;
       L2 : assert x = 17 ;
            foo() ;
            assert y = 22 
end algorithm

--------- MODULE Test -------
(* \* xxxx *) 

\*  (* *)
EXTENDS Sequences, Naturals, TLC


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-648cb8f5989caacb85bf4050478c7a20
VARIABLES x, y, pc, stack

vars == << x, y, pc, stack >>

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ stack = << >>
        /\ pc = "L1"

Q == /\ pc = "Q"
     /\ TRUE
     /\ IF TRUE
           THEN /\ IF TRUE
                      THEN /\ y' = 22
                      ELSE /\ y' = 42
           ELSE /\ LET a == 47 IN
                     LET b == 77 IN
                       y' = 27
     /\ pc' = Head(stack).pc
     /\ stack' = Tail(stack)
     /\ x' = x

Bar == Q

L1 == /\ pc = "L1"
      /\ y' = 1
      /\ pc' = "L3"
      /\ UNCHANGED << x, stack >>

L3 == /\ pc = "L3"
      /\ TRUE
      /\ IF x > 0
            THEN /\ IF TRUE
                       THEN /\ IF TRUE
                                  THEN /\ y' = 22
                                  ELSE /\ y' = 42
                       ELSE /\ LET a == 47 IN
                                 LET b == 77 IN
                                   y' = 27
                 /\ x' = x
            ELSE /\ x' = 17
                 /\ y' = y
      /\ pc' = "L2"
      /\ stack' = stack

L2 == /\ pc = "L2"
      /\ Assert(x = 17, "Failure of assertion at line 20, column 13.")
      /\ IF TRUE
            THEN /\ IF TRUE
                       THEN /\ y' = 22
                       ELSE /\ y' = 42
            ELSE /\ LET a == 47 IN
                      LET b == 77 IN
                        y' = 27
      /\ Assert(y' = 22, "Failure of assertion at line 22, column 13.")
      /\ pc' = "Done"
      /\ UNCHANGED << x, stack >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Bar \/ L1 \/ L3 \/ L2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-025c418c95de365cc2a03da9bdd7e60c

============================================
