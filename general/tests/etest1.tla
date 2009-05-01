--------------- MODULE etest1 -------------

(* Test that TLC complains if an operator is called with too many arguments. *)

EXTENDS TLC

VARIABLE x
Type == x \in BOOLEAN
Init == 
  /\ Print("Should complain that operator Foo is called with too many arguments", TRUE)
  /\ x = TRUE

Next == UNCHANGED x


Foo(a) == a 

Inv ==  Foo(x, x)

=========================================
