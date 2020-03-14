------------------ MODULE  TestReplace ----------------- 
EXTENDS Naturals, TLC, Sequences


(**********************
--algorithm TestReplace
macro IncrementX(u)
  begin X := X + u 
  end macro

procedure Bar(u, v)
 begin a: assert u = v;
          return;
 end procedure

procedure Foo1(u, v)
 variable X = 0; Y = X ;
 begin
 a : assert Y = X ;
 b : while Y = X do 
         Y := Y - 1;
     end while ;
     assert Y = X - 1;
     with id = X do assert id = 0  end with ;
     if X = 0
       then  c: call Bar(X, 0)
       else  assert FALSE 
     end if ;
 d : print <<X, " = 0">> ;
     IncrementX(X+1) ;
     assert X = 1 ;
 e:  return 
end procedure

procedure Foo2(u, v)
 variable X = 9; Z = X ;
 begin
 a : assert Z = X ;
 b : while Z = X do 
         Z := Z - 1;
     end while ;
     assert Z = X - 1;
     with id = X do assert id = 9  end with ;
     if X = 9
       then  c: call Bar(X, 9)
        
       else  assert FALSE 
     end if ;
 d : print <<X, " = 9">> ;
     IncrementX(X+1) ;
     assert X = 19 ;
 e:    return 
end procedure

begin
start : call Foo1(1, 2) ;
b : call Foo2(1, 2) ;
end algorithm

***********************)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a373e52549e281416ed7cb70fa982188
\* Label a of procedure Bar at line 12 col 11 changed to a_
\* Label a of procedure Foo1 at line 19 col 6 changed to a_F
\* Label b of procedure Foo1 at line 20 col 6 changed to b_
\* Label c of procedure Foo1 at line 26 col 17 changed to c_
\* Label d of procedure Foo1 at line 29 col 6 changed to d_
\* Label e of procedure Foo1 at line 32 col 6 changed to e_
\* Label b of procedure Foo2 at line 39 col 6 changed to b_F
\* Procedure variable X of procedure Foo1 at line 17 col 11 changed to X_
\* Parameter u of procedure Bar at line 11 col 15 changed to u_
\* Parameter v of procedure Bar at line 11 col 18 changed to v_
\* Parameter u of procedure Foo1 at line 16 col 16 changed to u_F
\* Parameter v of procedure Foo1 at line 16 col 19 changed to v_F
CONSTANT defaultInitValue
VARIABLES pc, stack, u_, v_, u_F, v_F, X_, Y, u, v, X, Z

vars == << pc, stack, u_, v_, u_F, v_F, X_, Y, u, v, X, Z >>

Init == (* Procedure Bar *)
        /\ u_ = defaultInitValue
        /\ v_ = defaultInitValue
        (* Procedure Foo1 *)
        /\ u_F = defaultInitValue
        /\ v_F = defaultInitValue
        /\ X_ = 0
        /\ Y = X_
        (* Procedure Foo2 *)
        /\ u = defaultInitValue
        /\ v = defaultInitValue
        /\ X = 9
        /\ Z = X
        /\ stack = << >>
        /\ pc = "start"

a_ == /\ pc = "a_"
      /\ Assert(u_ = v_, "Failure of assertion at line 12, column 11.")
      /\ pc' = Head(stack).pc
      /\ u_' = Head(stack).u_
      /\ v_' = Head(stack).v_
      /\ stack' = Tail(stack)
      /\ UNCHANGED << u_F, v_F, X_, Y, u, v, X, Z >>

Bar == a_

a_F == /\ pc = "a_F"
       /\ Assert(Y = X_, "Failure of assertion at line 19, column 6.")
       /\ pc' = "b_"
       /\ UNCHANGED << stack, u_, v_, u_F, v_F, X_, Y, u, v, X, Z >>

b_ == /\ pc = "b_"
      /\ IF Y = X_
            THEN /\ Y' = Y - 1
                 /\ pc' = "b_"
            ELSE /\ Assert(Y = X_ - 1, 
                           "Failure of assertion at line 23, column 6.")
                 /\ LET id == X_ IN
                      Assert(id = 0, 
                             "Failure of assertion at line 24, column 21.")
                 /\ IF X_ = 0
                       THEN /\ pc' = "c_"
                       ELSE /\ Assert(FALSE, 
                                      "Failure of assertion at line 27, column 14.")
                            /\ pc' = "d_"
                 /\ Y' = Y
      /\ UNCHANGED << stack, u_, v_, u_F, v_F, X_, u, v, X, Z >>

c_ == /\ pc = "c_"
      /\ /\ stack' = << [ procedure |->  "Bar",
                          pc        |->  "d_",
                          u_        |->  u_,
                          v_        |->  v_ ] >>
                      \o stack
         /\ u_' = X_
         /\ v_' = 0
      /\ pc' = "a_"
      /\ UNCHANGED << u_F, v_F, X_, Y, u, v, X, Z >>

d_ == /\ pc = "d_"
      /\ PrintT(<<X_, " = 0">>)
      /\ X_' = X_ + (X_+1)
      /\ Assert(X_' = 1, "Failure of assertion at line 31, column 6.")
      /\ pc' = "e_"
      /\ UNCHANGED << stack, u_, v_, u_F, v_F, Y, u, v, X, Z >>

e_ == /\ pc = "e_"
      /\ pc' = Head(stack).pc
      /\ X_' = Head(stack).X_
      /\ Y' = Head(stack).Y
      /\ u_F' = Head(stack).u_F
      /\ v_F' = Head(stack).v_F
      /\ stack' = Tail(stack)
      /\ UNCHANGED << u_, v_, u, v, X, Z >>

Foo1 == a_F \/ b_ \/ c_ \/ d_ \/ e_

a == /\ pc = "a"
     /\ Assert(Z = X, "Failure of assertion at line 38, column 6.")
     /\ pc' = "b_F"
     /\ UNCHANGED << stack, u_, v_, u_F, v_F, X_, Y, u, v, X, Z >>

b_F == /\ pc = "b_F"
       /\ IF Z = X
             THEN /\ Z' = Z - 1
                  /\ pc' = "b_F"
             ELSE /\ Assert(Z = X - 1, 
                            "Failure of assertion at line 42, column 6.")
                  /\ LET id == X IN
                       Assert(id = 9, 
                              "Failure of assertion at line 43, column 21.")
                  /\ IF X = 9
                        THEN /\ pc' = "c"
                        ELSE /\ Assert(FALSE, 
                                       "Failure of assertion at line 47, column 14.")
                             /\ pc' = "d"
                  /\ Z' = Z
       /\ UNCHANGED << stack, u_, v_, u_F, v_F, X_, Y, u, v, X >>

c == /\ pc = "c"
     /\ /\ stack' = << [ procedure |->  "Bar",
                         pc        |->  "d",
                         u_        |->  u_,
                         v_        |->  v_ ] >>
                     \o stack
        /\ u_' = X
        /\ v_' = 9
     /\ pc' = "a_"
     /\ UNCHANGED << u_F, v_F, X_, Y, u, v, X, Z >>

d == /\ pc = "d"
     /\ PrintT(<<X, " = 9">>)
     /\ X' = X + (X+1)
     /\ Assert(X' = 19, "Failure of assertion at line 51, column 6.")
     /\ pc' = "e"
     /\ UNCHANGED << stack, u_, v_, u_F, v_F, X_, Y, u, v, Z >>

e == /\ pc = "e"
     /\ pc' = Head(stack).pc
     /\ X' = Head(stack).X
     /\ Z' = Head(stack).Z
     /\ u' = Head(stack).u
     /\ v' = Head(stack).v
     /\ stack' = Tail(stack)
     /\ UNCHANGED << u_, v_, u_F, v_F, X_, Y >>

Foo2 == a \/ b_F \/ c \/ d \/ e

start == /\ pc = "start"
         /\ /\ stack' = << [ procedure |->  "Foo1",
                             pc        |->  "b",
                             X_        |->  X_,
                             Y         |->  Y,
                             u_F       |->  u_F,
                             v_F       |->  v_F ] >>
                         \o stack
            /\ u_F' = 1
            /\ v_F' = 2
         /\ X_' = 0
         /\ Y' = X_'
         /\ pc' = "a_F"
         /\ UNCHANGED << u_, v_, u, v, X, Z >>

b == /\ pc = "b"
     /\ /\ stack' = << [ procedure |->  "Foo2",
                         pc        |->  "Done",
                         X         |->  X,
                         Z         |->  Z,
                         u         |->  u,
                         v         |->  v ] >>
                     \o stack
        /\ u' = 1
        /\ v' = 2
     /\ X' = 9
     /\ Z' = X'
     /\ pc' = "a"
     /\ UNCHANGED << u_, v_, u_F, v_F, X_, Y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Bar \/ Foo1 \/ Foo2 \/ start \/ b
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-424be35f7792f0f2c25e136cc792e4c5

==================================================

