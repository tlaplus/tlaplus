------------------------- MODULE test215 ------------------------- 
\* Test of constraints on levels of temporal operators that
\* outlaw any form of raw TLA.

VARIABLE x

a == x ~> []x
b == x' ~> []x    \* ERROR
c == []x ~> x'    \* ERROR

d == x -+-> []x
e == x' -+-> []x  \* ERROR
f == []x -+-> x'  \* ERROR

g == <><<x'>>_x
h == <>(x')       \* ERROR

foo == [][x']_x

bar == [](x')    \* ERROR

m == \A i \in {}, j \in x : []x
n == \A i \in {}, j \in x' : []x   \* ERROR

mm == \E i \in {}, j \in x : []x
nn == \E i \in {}, j \in x' : []x   \* ERROR

m2 == \A i \in x' : x'
=======================================================================