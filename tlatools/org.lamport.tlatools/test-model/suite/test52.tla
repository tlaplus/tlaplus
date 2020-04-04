----------------------   MODULE test52 -----------------------

\* Test of prefix and postfix operators as arguments

EXTENDS TLC

VARIABLES x, y

BoxTest(-._) == -(x=0)
Foo1 == BoxTest([])
Foo2 == BoxTest(<>)

-. a == {{"a"}, {"b"}} \ a
a ^+  == {{"a"}, {"b"}} \ a
a ^*  == {{"a"}, {"b"}} \ a
a ^#  == {{"a"}, {"b"}} \ a

SetOpTest(Foo(_)) == Foo({{"b"}, {"c"}})
DomainTest(Foo(_)) == Foo([i\in {"a", "b"} |-> i])

ASSUME
  /\ Print("Test1 Begun", TRUE)
  /\ SetOpTest(-.) =  - {{"b"}, {"c"}}
  /\ SetOpTest(^+) =   {{"b"}, {"c"}} ^+
  /\ SetOpTest(^*) =   {{"b"}, {"c"}} ^*
  /\ SetOpTest(^#) =   {{"b"}, {"c"}} ^#
  /\ SetOpTest(SUBSET) = SUBSET {{"b"}, {"c"}}
  /\ SetOpTest(UNION) = UNION {{"b"}, {"c"}}
  /\ DomainTest(DOMAIN) = DOMAIN [i\in {"a", "b"} |-> i]
  /\ Print("Test1 Finished", TRUE)


Init == /\ x = {"a"}
        /\ y = {"a"}
Next == /\ x'= x \cup {"a"}
        /\ y'= y \cup {"b"}
Spec == Init /\ [][Next]_<<x, y>>

EnabledTest(Foo(_)) == Foo(x'=x)
UnchangedTest(Foo(_)) == Foo(x)
PrimeTest(Foo(_)) == Foo(x) = x

Invariant ==
 /\ EnabledTest(ENABLED)

ImpliedAction ==
 /\ UnchangedTest(UNCHANGED)
 /\ PrimeTest(')

Property == [][ImpliedAction]_<<x, y>>

==================================================================
\* Prefix Operators
~
ENABLED
UNCHANGED
[]
<>
SUBSET
UNION
DOMAIN
-

\* Postfix Operators
\* Predefined
'

\* Undefined
^+
^*
^#
