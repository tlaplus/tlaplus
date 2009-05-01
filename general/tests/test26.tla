--------------- MODULE test26 -------------

(* Test of LET *)

EXTENDS TLC, Naturals, Sequences

VARIABLE x

Init ==  x = 0

FcnSubst(f, e(_)) ==
  (* A recursive definition of [i \in DOMAIN f |-> e(i)] *)
  LET Range == {f[i] : i \in DOMAIN f}
      FSet == UNION { [U -> Range] : U \in SUBSET DOMAIN f}
      FSub[g \in FSet] == 
        IF g = << >> 
          THEN g
          ELSE LET el == CHOOSE el \in DOMAIN g : TRUE
               IN  [ i \in DOMAIN g |-> 
                     IF i = el 
                      THEN e(i)
                      ELSE FSub[[j \in (DOMAIN g) \ {el} |-> f[j]]][i]]
  IN FSub[f]


Inv == 

  /\ LET A == {}
         B == A
     IN  IF B = {}
           THEN Print("Test 1 OK", TRUE)
           ELSE Assert(FALSE, "Test 1 Failed")

  /\ LET A == {}
         B == A
         C[i \in B] == 17
     IN  IF C = << >> 
           THEN Print("Test 2 OK", TRUE)
           ELSE Assert(FALSE, "Test 2 Failed")

  /\ LET e(i) == i+1
     IN  IF FcnSubst(<<1,2,3>>, e) = <<2,3,4>>
           THEN Print("Test 3 OK", TRUE)
           ELSE Assert(FALSE, "Test 3 Failed")
           
Next ==  UNCHANGED x
=========================================
