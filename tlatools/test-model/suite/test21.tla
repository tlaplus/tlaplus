--------------- MODULE test21 -------------

(* Test of priming and variable confusion *)

EXTENDS Naturals, Sequences, TLC

Bar(z)    == z' = 2
Foo(y)    == y = 2
FooBar(y) == y = 1

VARIABLE x, y

LetTest == LET s == x=1
           IN  s


Op(a) ==  x+a

Init == /\ x = 1
        /\ y = 3
Next == 

  \/ /\ x = 1
     /\ x'=x+1
     /\ y' = y
     /\ IF Bar(x)
          THEN Print("Test 1 OK", TRUE)
          ELSE Assert(FALSE, "Test 1 Failed")

  \/ /\ x = 1
     /\ x'=x+1
     /\ y' = y
     /\ IF Foo(x)'
          THEN Print("Test 2 OK", TRUE)
          ELSE Assert(FALSE, "Test 2 Failed")

  \/ /\ x = 1
     /\ x'=x+1
     /\ y' = y
     /\ IF FooBar(x)
          THEN Print("Test 3 OK", TRUE)
          ELSE Assert(FALSE, "Test 3 Failed")
     /\ IF LetTest' THEN Assert(FALSE, "Test 4 Failed")
                    ELSE Print("Test 4 OK", TRUE)
     /\ LET a == x
        IN  IF a' = 2 THEN Print("Test 5 OK", TRUE)
                      ELSE Assert(FALSE, "Test 5 Failed")

     /\ IF FooBar(x)' THEN Assert(FALSE, "Test 6 Failed")
                      ELSE Print("Test 6 OK", TRUE)

     /\ IF FooBar(x') THEN Assert(FALSE, "Test 7 Failed")
                      ELSE Print("Test 7 OK", TRUE)

  \/ IF (x = 1)
       THEN /\ x'=x+1
            /\ y'=y
            /\ Print("Test 8 OK", TRUE)
       ELSE /\ x'=x+1
            /\ y'=y
            /\ Print("Test 12 OK", FALSE)  

  \/ /\ x = 1
     /\ x'=x+1
     /\ y'=y
     /\ IF Op(1)' = 3
          THEN Print("Test 9 OK", TRUE)
          ELSE Assert(FALSE, "Test 9 Failed")
     /\ IF LET LetOp(a) ==  x+a
           IN  LetOp(1)' = 3
          THEN Print("Test 10 OK", TRUE)
          ELSE Assert(FALSE, "Test 10 Failed")

     /\ IF (LET LetOp(a) ==  x+a
            IN  LetOp(1) = 3     )'
          THEN Print("Test 11 OK", TRUE)
          ELSE Assert(FALSE, "Test 11 Failed")

  \/ UNCHANGED <<x,y>>

Inv == TRUE

=========================================
