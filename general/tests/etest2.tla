--------------- MODULE etest2 -------------

(* Test that TLC complains if a operator is called with too few arguments. *)

EXTENDS TLC

VARIABLE x
Type == x \in BOOLEAN
Init == 
  /\ Print("Should complain that operator Foo is called with too few arguments", TRUE)
  /\ x = TRUE

Next == UNCHANGED x


Foo(a, b) == a /\ b

Inv ==  Foo(x)

=========================================
