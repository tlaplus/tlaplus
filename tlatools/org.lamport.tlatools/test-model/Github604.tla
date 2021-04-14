------ MODULE Github604 ------
EXTENDS Naturals

VARIABLE 
    \* @type: Int;  \* Apalache type annotation
    x

Init == x = 0

Next == x' \in 0..3

Spec == Init /\ [][Next]_x \* /\ WF_x(Next)

-----------------------------------------------

USE DEF Init, Next, Spec

Prop01 == <>(TRUE)
THEOREM Spec => Prop01 BY DEF Prop01 

Prop02 == [](TRUE)             \* TLC checks Prop02 as part of safety checking.
THEOREM Spec => Prop02 BY DEF Prop02

Prop03 == <>[](TRUE)
THEOREM Spec => Prop03 OMITTED \* Not proved by TLAPS 1.4.5 (feels inconsistent WRT 01 & 02)

-----------------------------------------------

\* Prop04 & 05 take a different code path of TLC compared to
\* 06 & 07 despite being logically equivalent.

Prop04 == FALSE ~> TRUE
THEOREM Spec => Prop04 OMITTED \* Not proved by TLAPS 1.4.5

Prop05 == FALSE ~> FALSE
THEOREM Spec => Prop05 OMITTED \* Not proved by TLAPS 1.4.5
    
Prop06 == TRUE ~> TRUE
THEOREM Spec => Prop06 OMITTED \* Not proved by TLAPS 1.4.5

Prop07 == [](FALSE => <>TRUE)
THEOREM Spec => Prop07 OMITTED \* Not proved by TLAPS 1.4.5

Prop08 == [](FALSE => <>FALSE)
THEOREM Spec => Prop08 OMITTED \* Not proved by TLAPS 1.4.5

\* state-level

Prop09 == [](FALSE => <>(x=x))
THEOREM Spec => Prop09 OMITTED \* Not proved by TLAPS 1.4.5

Prop10 == [](FALSE => <>(x#x))
THEOREM Spec => Prop10 OMITTED \* Not proved by TLAPS 1.4.5

-----------------------------------------------

Prop11 == <>(x=x)
THEOREM Spec => Prop11 OMITTED \* Not proved by TLAPS 1.4.5
   
Prop12 == [](x=x)
THEOREM Spec => Prop12 OMITTED \* Not proved by TLAPS 1.4.5
    
Prop13 == <>[](x=x)
THEOREM Spec => Prop13 OMITTED \* Not proved by TLAPS 1.4.5

-----------------------------------------------

Prop14 == TRUE ~> []TRUE /\ (FALSE ~> []TRUE)

Prop15 == TRUE ~> <>TRUE /\ (FALSE ~> <>TRUE)

Prop16 == TRUE ~> <>[]TRUE /\ (FALSE ~> <>[]TRUE)

-----------------------------------------------

Prop17 == TRUE ~> [](x=x) /\ (FALSE ~> [](x=x))

Prop18 == TRUE ~> <>(x=x) /\ (FALSE ~> <>(x=x))

Prop19 == TRUE ~> <>[](x=x) /\ (FALSE ~> <>[](x=x))

Prop20 == (FALSE /\ (x=x)) ~> (<>[](x#x))

====

---- CONFIG Github604 ----
SPECIFICATION Spec
PROPERTY
    Prop01  \* Fixed as part of Github #604
    Prop02
    Prop03
    Prop04  \* Fixed as part of Github #604
    Prop05  \* Fixed as part of Github #604 
    Prop06
    Prop07  \* Fixed as part of Github #604
    Prop08  \* Fixed as part of Github #604
    Prop09  \* Fixed as part of Github #604
    Prop10  \* Fixed as part of Github #604
    Prop11
    Prop12
    Prop13
    Prop14 \* Fixed as part of Github #604
    Prop15 \* Fixed as part of Github #604
    Prop16 \* Fixed as part of Github #604
    Prop17 \* Fixed as part of Github #604
    Prop18 \* Fixed as part of Github #604
    Prop19 \* Fixed as part of Github #604
    Prop20
====
