The translator is not properly initializing the local procedure variables.
The assertions indicate how they should be initialized.  (The OldPlusCal
and Pcal translations have this problem too.)

----------------------------- MODULE CallReturn2 ----------------------------- 
EXTENDS Naturals, Sequences, TLC


(*   
--algorithm Test
   variable depth = 3
   procedure P(a = 7) 
      variable x = a ; y = x+1 ;
      begin P1: assert a = 1;
                assert x = a;
                assert y = a+1;
                return;
      end procedure 
  procedure Q() 
     begin Q1: call P(1) ;
              return ;
      end procedure 
  procedure PP(aa = 7)
      variable xx = aa ; yy = xx+1 ;
      begin PP1: if depth > 0
                  then assert aa = 1;
                     assert xx = aa;
                     assert yy = aa+1;
                     depth := depth - 1 ;
                     call PP(1) ;
                     return;
                  else return 
                end if 
      end procedure 
  procedure R(r = 0)
     variable x
     begin R1: x := 2 ;
           R2: call S(x) ;
               return 
     end procedure
  procedure S(s)
    begin S1: assert s = 2 ;
               return ;
    end procedure 
 begin A: call P(1) ;
       B: call Q() ;
       C: call PP(1) ;
  end algorithm
*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-84a5cdf59d68214ad905732a585890ae
\* Procedure variable x of procedure P at line 13 col 16 changed to x_
CONSTANT defaultInitValue
VARIABLES depth, pc, stack, a, x_, y, aa, xx, yy, r, x, s

vars == << depth, pc, stack, a, x_, y, aa, xx, yy, r, x, s >>

Init == (* Global variables *)
        /\ depth = 3
        (* Procedure P *)
        /\ a = 7
        /\ x_ = a
        /\ y = x_+1
        (* Procedure PP *)
        /\ aa = 7
        /\ xx = aa
        /\ yy = xx+1
        (* Procedure R *)
        /\ r = 0
        /\ x = defaultInitValue
        (* Procedure S *)
        /\ s = defaultInitValue
        /\ stack = << >>
        /\ pc = "A"

P1 == /\ pc = "P1"
      /\ Assert(a = 1, "Failure of assertion at line 14, column 17.")
      /\ Assert(x_ = a, "Failure of assertion at line 15, column 17.")
      /\ Assert(y = a+1, "Failure of assertion at line 16, column 17.")
      /\ pc' = Head(stack).pc
      /\ x_' = Head(stack).x_
      /\ y' = Head(stack).y
      /\ a' = Head(stack).a
      /\ stack' = Tail(stack)
      /\ UNCHANGED << depth, aa, xx, yy, r, x, s >>

P == P1

Q1 == /\ pc = "Q1"
      /\ /\ a' = 1
         /\ stack' = << [ procedure |->  "P",
                          pc        |->  Head(stack).pc,
                          x_        |->  x_,
                          y         |->  y,
                          a         |->  a ] >>
                      \o Tail(stack)
      /\ x_' = a'
      /\ y' = x_'+1
      /\ pc' = "P1"
      /\ UNCHANGED << depth, aa, xx, yy, r, x, s >>

Q == Q1

PP1 == /\ pc = "PP1"
       /\ IF depth > 0
             THEN /\ Assert(aa = 1, 
                            "Failure of assertion at line 26, column 24.")
                  /\ Assert(xx = aa, 
                            "Failure of assertion at line 27, column 22.")
                  /\ Assert(yy = aa+1, 
                            "Failure of assertion at line 28, column 22.")
                  /\ depth' = depth - 1
                  /\ aa' = 1
                  /\ xx' = aa'
                  /\ yy' = xx'+1
                  /\ pc' = "PP1"
                  /\ stack' = stack
             ELSE /\ pc' = Head(stack).pc
                  /\ xx' = Head(stack).xx
                  /\ yy' = Head(stack).yy
                  /\ aa' = Head(stack).aa
                  /\ stack' = Tail(stack)
                  /\ depth' = depth
       /\ UNCHANGED << a, x_, y, r, x, s >>

PP == PP1

R1 == /\ pc = "R1"
      /\ x' = 2
      /\ pc' = "R2"
      /\ UNCHANGED << depth, stack, a, x_, y, aa, xx, yy, r, s >>

R2 == /\ pc = "R2"
      /\ /\ s' = x
         /\ stack' = << [ procedure |->  "S",
                          pc        |->  Head(stack).pc,
                          s         |->  s ] >>
                      \o Tail(stack)
         /\ x' = Head(stack).x
      /\ pc' = "S1"
      /\ UNCHANGED << depth, a, x_, y, aa, xx, yy, r >>

R == R1 \/ R2

S1 == /\ pc = "S1"
      /\ Assert(s = 2, "Failure of assertion at line 42, column 15.")
      /\ pc' = Head(stack).pc
      /\ s' = Head(stack).s
      /\ stack' = Tail(stack)
      /\ UNCHANGED << depth, a, x_, y, aa, xx, yy, r, x >>

S == S1

A == /\ pc = "A"
     /\ /\ a' = 1
        /\ stack' = << [ procedure |->  "P",
                         pc        |->  "B",
                         x_        |->  x_,
                         y         |->  y,
                         a         |->  a ] >>
                     \o stack
     /\ x_' = a'
     /\ y' = x_'+1
     /\ pc' = "P1"
     /\ UNCHANGED << depth, aa, xx, yy, r, x, s >>

B == /\ pc = "B"
     /\ stack' = << [ procedure |->  "Q",
                      pc        |->  "C" ] >>
                  \o stack
     /\ pc' = "Q1"
     /\ UNCHANGED << depth, a, x_, y, aa, xx, yy, r, x, s >>

C == /\ pc = "C"
     /\ /\ aa' = 1
        /\ stack' = << [ procedure |->  "PP",
                         pc        |->  "Done",
                         xx        |->  xx,
                         yy        |->  yy,
                         aa        |->  aa ] >>
                     \o stack
     /\ xx' = aa'
     /\ yy' = xx'+1
     /\ pc' = "PP1"
     /\ UNCHANGED << depth, a, x_, y, r, x, s >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == P \/ Q \/ PP \/ R \/ S \/ A \/ B \/ C
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c8e76178d4d24aee35fa88a19dd439d8
=============================================================================
