------------------------------ MODULE K ------------------------------

EXTENDS Naturals

Foo(Op(_), S) == \A s \in S: Op(s)

Bar(S) == Foo(LAMBDA e: e \in Nat, S)

VARIABLE x

Spec == x = Bar({1,2,3}) /\ [][UNCHANGED x]_x 
============
