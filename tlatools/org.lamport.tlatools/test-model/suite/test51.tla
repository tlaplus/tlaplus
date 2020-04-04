----------------------   MODULE test51 -----------------------
\* Test of handling of infix operator symbols

EXTENDS TLC

\* Test parser on action/temporal infix operators

FooA == INSTANCE test51a
FooB == INSTANCE test51b

TempTest(_+_) == TRUE + FALSE
Foo1 == TempTest(-+->)
Foo2 == TempTest(~>)
Foo3 == TempTest(\cdot)

\* Definining all undefined infix operators 

a + b == {a, b}
a - b == {a, b}
a * b == {a, b}
a / b == {a, b}
a ..b == {a, b}
a < b == {a, b}
a > b == {a, b}
a \leq b == {a, b}
a \geq b == {a, b}
a % b == {a, b}
a ^b == {a, b}
a \o b == {a, b}
a ++ b == {a, b}
a \div b == {a, b}
a ...b == {a, b}
a -- b == {a, b}
a (+)b == {a, b}
a (-)b == {a, b}
a (\X)b == {a, b}
a (/)b == {a, b}
a (.)b == {a, b}
a ** b == {a, b}
a \sqcap b == {a, b}
a // b == {a, b}
a \prec b == {a, b}
a \succ b == {a, b}
a \preceq b == {a, b}
a \succeq b == {a, b}
a \sqcup b == {a, b}
a ^^b == {a, b}
a \ll b == {a, b}
a \gg b == {a, b}
a <: b == {a, b}
a & b == {a, b}
a && b == {a, b}
a \sqsubset b == {a, b}
a \sqsupset b == {a, b}
a \sqsubseteq b == {a, b}
a \sqsupseteq b == {a, b}
a | b == {a, b}
a || b == {a, b}
a \subset b == {a, b}
a \supset b == {a, b}
a \supseteq b == {a, b}
a \star b == {a, b}
a %% b == {a, b}
a |- b == {a, b}
a -|b == {a, b}
a |= b == {a, b}
a =|b == {a, b}
a \bullet b == {a, b}
a ##b == {a, b}
a \sim b == {a, b}
a \simeq b == {a, b}
a \approx b == {a, b}
a \cong b == {a, b}
a $b == {a, b}
a $$b == {a, b}
a := b == {a, b}
a ::= b == {a, b}
a \asymp b == {a, b}
a \doteq b == {a, b}
a ?? b == {a, b}
a !! b == {a, b}
a \propto b == {a, b}
a \wr b == {a, b}
a \uplus b == {a, b}
a \bigcirc b == {a, b}

TestOpArg(Foo(_,_)) == Foo("a", "b")

TestTLCOps(colongt(_,_), atat(_,_)) ==
   atat( colongt(1, "ab"), colongt(2, "cd"))
 \* 1 :> "ab" @@ 2 :> "cd"

TestDefinedSetOp(Foo(_,_)) == Foo({"a", "b"}, {"b", "c"})
TestDefinedBooleanOp(Foo(_,_)) == Foo(TRUE,FALSE)
TestIn(Foo(_,_)) == Foo("a", {"b", "c"})

ASSUME
  /\ IF TestOpArg(+ ) = {"a", "b"}
       THEN Print("Test 1 OK", TRUE)
       ELSE Assert(FALSE, "Test 1 Failed")
  /\ IF TestOpArg( - ) = {"a", "b"}
       THEN Print("Test 2 OK", TRUE)
       ELSE Assert(FALSE, "Test 2 Failed")
  /\ IF TestOpArg( * ) = {"a", "b"}
       THEN Print("Test 3 OK", TRUE)
       ELSE Assert(FALSE, "Test 3 Failed")
  /\ IF TestOpArg(/ ) = {"a", "b"}
       THEN Print("Test 4 OK", TRUE)
       ELSE Assert(FALSE, "Test 4 Failed")
  /\ IF TestOpArg(..) = {"a", "b"}
       THEN Print("Test 5 OK", TRUE)
       ELSE Assert(FALSE, "Test 5 Failed")
  /\ IF TestOpArg(< ) = {"a", "b"}
       THEN Print("Test 6 OK", TRUE)
       ELSE Assert(FALSE, "Test 6 Failed")
  /\ IF TestOpArg(> ) = {"a", "b"}
       THEN Print("Test 7 OK", TRUE)
       ELSE Assert(FALSE, "Test 7 Failed")
  /\ IF TestOpArg(\leq ) = {"a", "b"}
       THEN Print("Test 8 OK", TRUE)
       ELSE Assert(FALSE, "Test 8 Failed")
  /\ IF TestOpArg(=<) = {"a", "b"}
       THEN Print("Test 9 OK", TRUE)
       ELSE Assert(FALSE, "Test 9 Failed")
  /\ IF TestOpArg(<=) = {"a", "b"}
       THEN Print("Test 10 OK", TRUE)
       ELSE Assert(FALSE, "Test 10 Failed")
  /\ IF TestOpArg(\geq ) = {"a", "b"}
       THEN Print("Test 11 OK", TRUE)
       ELSE Assert(FALSE, "Test 11 Failed")
  /\ IF TestOpArg(>=) = {"a", "b"}
       THEN Print("Test 12 OK", TRUE)
       ELSE Assert(FALSE, "Test 12 Failed")
  /\ IF TestOpArg(% ) = {"a", "b"}
       THEN Print("Test 13 OK", TRUE)
       ELSE Assert(FALSE, "Test 13 Failed")
  /\ IF TestOpArg(^) = {"a", "b"}
       THEN Print("Test 14 OK", TRUE)
       ELSE Assert(FALSE, "Test 14 Failed")
  /\ IF TestOpArg(\circ ) = {"a", "b"}
       THEN Print("Test 15 OK", TRUE)
       ELSE Assert(FALSE, "Test 15 Failed")
  /\ IF TestOpArg(\o) = {"a", "b"}
       THEN Print("Test 16 OK", TRUE)
       ELSE Assert(FALSE, "Test 16 Failed")
  /\ IF TestOpArg(++ ) = {"a", "b"}
       THEN Print("Test 17 OK", TRUE)
       ELSE Assert(FALSE, "Test 17 Failed")
  /\ IF TestOpArg(\div ) = {"a", "b"}
       THEN Print("Test 18 OK", TRUE)
       ELSE Assert(FALSE, "Test 18 Failed")
  /\ IF TestOpArg(...) = {"a", "b"}
       THEN Print("Test 19 OK", TRUE)
       ELSE Assert(FALSE, "Test 19 Failed")
  /\ IF TestOpArg(-- ) = {"a", "b"}
       THEN Print("Test 20 OK", TRUE)
       ELSE Assert(FALSE, "Test 20 Failed")
  /\ IF TestOpArg(\oplus ) = {"a", "b"}
       THEN Print("Test 21 OK", TRUE)
       ELSE Assert(FALSE, "Test 21 Failed")
  /\ IF TestOpArg((+)) = {"a", "b"}
       THEN Print("Test 22 OK", TRUE)
       ELSE Assert(FALSE, "Test 22 Failed")
  /\ IF TestOpArg(\ominus ) = {"a", "b"}
       THEN Print("Test 23 OK", TRUE)
       ELSE Assert(FALSE, "Test 23 Failed")
  /\ IF TestOpArg((-)) = {"a", "b"}
       THEN Print("Test 24 OK", TRUE)
       ELSE Assert(FALSE, "Test 24 Failed")
  /\ IF TestOpArg(\otimes ) = {"a", "b"}
       THEN Print("Test 25 OK", TRUE)
       ELSE Assert(FALSE, "Test 25 Failed")
  /\ IF TestOpArg((\X)) = {"a", "b"}
       THEN Print("Test 26 OK", TRUE)
       ELSE Assert(FALSE, "Test 26 Failed")
  /\ IF TestOpArg(\oslash ) = {"a", "b"}
       THEN Print("Test 27 OK", TRUE)
       ELSE Assert(FALSE, "Test 27 Failed")
  /\ IF TestOpArg((/)) = {"a", "b"}
       THEN Print("Test 28 OK", TRUE)
       ELSE Assert(FALSE, "Test 28 Failed")
  /\ IF TestOpArg(\odot ) = {"a", "b"}
       THEN Print("Test 29 OK", TRUE)
       ELSE Assert(FALSE, "Test 29 Failed")
  /\ IF TestOpArg((.)) = {"a", "b"}
       THEN Print("Test 30 OK", TRUE)
       ELSE Assert(FALSE, "Test 30 Failed")
  /\ IF TestOpArg( ** ) = {"a", "b"}
       THEN Print("Test 31 OK", TRUE)
       ELSE Assert(FALSE, "Test 31 Failed")
  /\ IF TestOpArg(\sqcap ) = {"a", "b"}
       THEN Print("Test 32 OK", TRUE)
       ELSE Assert(FALSE, "Test 32 Failed")
  /\ IF TestOpArg(// ) = {"a", "b"}
       THEN Print("Test 33 OK", TRUE)
       ELSE Assert(FALSE, "Test 33 Failed")
  /\ IF TestOpArg(\prec ) = {"a", "b"}
       THEN Print("Test 34 OK", TRUE)
       ELSE Assert(FALSE, "Test 34 Failed")
  /\ IF TestOpArg(\succ ) = {"a", "b"}
       THEN Print("Test 35 OK", TRUE)
       ELSE Assert(FALSE, "Test 35 Failed")
  /\ IF TestOpArg(\preceq ) = {"a", "b"}
       THEN Print("Test 36 OK", TRUE)
       ELSE Assert(FALSE, "Test 36 Failed")
  /\ IF TestOpArg(\succeq ) = {"a", "b"}
       THEN Print("Test 37 OK", TRUE)
       ELSE Assert(FALSE, "Test 37 Failed")
  /\ IF TestOpArg(\sqcup ) = {"a", "b"}
       THEN Print("Test 38 OK", TRUE)
       ELSE Assert(FALSE, "Test 38 Failed")
  /\ IF TestOpArg(^^) = {"a", "b"}
       THEN Print("Test 39 OK", TRUE)
       ELSE Assert(FALSE, "Test 39 Failed")
  /\ IF TestOpArg(\ll ) = {"a", "b"}
       THEN Print("Test 40 OK", TRUE)
       ELSE Assert(FALSE, "Test 40 Failed")
  /\ IF TestOpArg(\gg ) = {"a", "b"}
       THEN Print("Test 41 OK", TRUE)
       ELSE Assert(FALSE, "Test 41 Failed")
  /\ IF TestOpArg(<: ) = {"a", "b"}
       THEN Print("Test 42 OK", TRUE)
       ELSE Assert(FALSE, "Test 42 Failed")
  /\ IF TestOpArg(& ) = {"a", "b"}
       THEN Print("Test 43 OK", TRUE)
       ELSE Assert(FALSE, "Test 43 Failed")
  /\ IF TestOpArg(&& ) = {"a", "b"}
       THEN Print("Test 44 OK", TRUE)
       ELSE Assert(FALSE, "Test 44 Failed")
  /\ IF TestOpArg(\sqsubset ) = {"a", "b"}
       THEN Print("Test 45 OK", TRUE)
       ELSE Assert(FALSE, "Test 45 Failed")
  /\ IF TestOpArg(\sqsupset ) = {"a", "b"}
       THEN Print("Test 46 OK", TRUE)
       ELSE Assert(FALSE, "Test 46 Failed")
  /\ IF TestOpArg(\sqsubseteq ) = {"a", "b"}
       THEN Print("Test 47 OK", TRUE)
       ELSE Assert(FALSE, "Test 47 Failed")
  /\ IF TestOpArg(\sqsupseteq ) = {"a", "b"}
       THEN Print("Test 48 OK", TRUE)
       ELSE Assert(FALSE, "Test 48 Failed")
  /\ IF TestOpArg(| ) = {"a", "b"}
       THEN Print("Test 49 OK", TRUE)
       ELSE Assert(FALSE, "Test 49 Failed")
  /\ IF TestOpArg(|| ) = {"a", "b"}
       THEN Print("Test 50 OK", TRUE)
       ELSE Assert(FALSE, "Test 50 Failed")
  /\ IF TestOpArg(\subset ) = {"a", "b"}
       THEN Print("Test 51 OK", TRUE)
       ELSE Assert(FALSE, "Test 51 Failed")
  /\ IF TestOpArg(\supset ) = {"a", "b"}
       THEN Print("Test 52 OK", TRUE)
       ELSE Assert(FALSE, "Test 52 Failed")
  /\ IF TestOpArg(\supseteq ) = {"a", "b"}
       THEN Print("Test 53 OK", TRUE)
       ELSE Assert(FALSE, "Test 53 Failed")
  /\ IF TestOpArg(\star ) = {"a", "b"}
       THEN Print("Test 54 OK", TRUE)
       ELSE Assert(FALSE, "Test 54 Failed")
  /\ IF TestOpArg(%% ) = {"a", "b"}
       THEN Print("Test 55 OK", TRUE)
       ELSE Assert(FALSE, "Test 55 Failed")
  /\ IF TestOpArg(|- ) = {"a", "b"}
       THEN Print("Test 56 OK", TRUE)
       ELSE Assert(FALSE, "Test 56 Failed")
  /\ IF TestOpArg(-|) = {"a", "b"}
       THEN Print("Test 57 OK", TRUE)
       ELSE Assert(FALSE, "Test 57 Failed")
  /\ IF TestOpArg(|= ) = {"a", "b"}
       THEN Print("Test 58 OK", TRUE)
       ELSE Assert(FALSE, "Test 58 Failed")
  /\ IF TestOpArg(=|) = {"a", "b"}
       THEN Print("Test 59 OK", TRUE)
       ELSE Assert(FALSE, "Test 59 Failed")
  /\ IF TestOpArg(\bullet ) = {"a", "b"}
       THEN Print("Test 60 OK", TRUE)
       ELSE Assert(FALSE, "Test 60 Failed")
  /\ IF TestOpArg(##) = {"a", "b"}
       THEN Print("Test 61 OK", TRUE)
       ELSE Assert(FALSE, "Test 61 Failed")
  /\ IF TestOpArg(\sim ) = {"a", "b"}
       THEN Print("Test 62 OK", TRUE)
       ELSE Assert(FALSE, "Test 62 Failed")
  /\ IF TestOpArg(\simeq ) = {"a", "b"}
       THEN Print("Test 63 OK", TRUE)
       ELSE Assert(FALSE, "Test 63 Failed")
  /\ IF TestOpArg(\approx ) = {"a", "b"}
       THEN Print("Test 64 OK", TRUE)
       ELSE Assert(FALSE, "Test 64 Failed")
  /\ IF TestOpArg(\cong ) = {"a", "b"}
       THEN Print("Test 65 OK", TRUE)
       ELSE Assert(FALSE, "Test 65 Failed")
  /\ IF TestOpArg($) = {"a", "b"}
       THEN Print("Test 66 OK", TRUE)
       ELSE Assert(FALSE, "Test 66 Failed")
  /\ IF TestOpArg($$) = {"a", "b"}
       THEN Print("Test 67 OK", TRUE)
       ELSE Assert(FALSE, "Test 67 Failed")
  /\ IF TestOpArg(:= ) = {"a", "b"}
       THEN Print("Test 68 OK", TRUE)
       ELSE Assert(FALSE, "Test 68 Failed")
  /\ IF TestOpArg(::= ) = {"a", "b"}
       THEN Print("Test 69 OK", TRUE)
       ELSE Assert(FALSE, "Test 69 Failed")
  /\ IF TestOpArg(\asymp ) = {"a", "b"}
       THEN Print("Test 70 OK", TRUE)
       ELSE Assert(FALSE, "Test 70 Failed")
  /\ IF TestOpArg(\doteq ) = {"a", "b"}
       THEN Print("Test 71 OK", TRUE)
       ELSE Assert(FALSE, "Test 71 Failed")
  /\ IF TestOpArg(?? ) = {"a", "b"}
       THEN Print("Test 72 OK", TRUE)
       ELSE Assert(FALSE, "Test 72 Failed")
  /\ IF TestOpArg(!! ) = {"a", "b"}
       THEN Print("Test 73 OK", TRUE)
       ELSE Assert(FALSE, "Test 73 Failed")
  /\ IF TestOpArg(\propto ) = {"a", "b"}
       THEN Print("Test 74 OK", TRUE)
       ELSE Assert(FALSE, "Test 74 Failed")
  /\ IF TestOpArg(\wr ) = {"a", "b"}
       THEN Print("Test 75 OK", TRUE)
       ELSE Assert(FALSE, "Test 75 Failed")
  /\ IF TestOpArg(\uplus ) = {"a", "b"}
       THEN Print("Test 76 OK", TRUE)
       ELSE Assert(FALSE, "Test 76 Failed")
  /\ IF TestOpArg(\bigcirc ) = {"a", "b"}
       THEN Print("Test 77 OK", TRUE)
       ELSE Assert(FALSE, "Test 77 Failed")
  /\ IF TestTLCOps(:>, @@) =  1 :> "ab" @@ 2 :> "cd"
       THEN Print("Test 78 OK", TRUE)
       ELSE Assert(FALSE, "Test 78 Failed")
  /\ IF TestDefinedBooleanOp(=>) = (TRUE => FALSE)
       THEN Print("Test 79 OK", TRUE)
       ELSE Assert(FALSE, "Test 79 Failed")
  /\ IF TestDefinedBooleanOp(\equiv) = (TRUE \equiv FALSE)
       THEN Print("Test 80 OK", TRUE)
       ELSE Assert(FALSE, "Test 80 Failed")
  /\ IF TestDefinedBooleanOp(<=>) = (TRUE <=> FALSE)
       THEN Print("Test 81 OK", TRUE)
       ELSE Assert(FALSE, "Test 81 Failed")
\*  /\ Print("Test 82 fails because of parser bug", TRUE)
  /\ IF TestDefinedBooleanOp(/\) = (TRUE /\ FALSE)
       THEN Print("Test 82 OK", TRUE)
       ELSE Assert(FALSE, "Test 82 Failed")
  /\ IF TestDefinedBooleanOp(\land) = (TRUE \land FALSE)
       THEN Print("Test 83 OK", TRUE)
       ELSE Assert(FALSE, "Test 83 Failed")
\*  /\ Print("Test 84 fails because of parser bug", TRUE)
  /\ IF TestDefinedBooleanOp(\/) = (TRUE \/ FALSE)
       THEN Print("Test 84 OK", TRUE)
       ELSE Assert(FALSE, "Test 84 Failed")
  /\ IF TestDefinedBooleanOp(\lor) = (TRUE \lor FALSE)
       THEN Print("Test 85 OK", TRUE)
       ELSE Assert(FALSE, "Test 85 Failed")
  /\ IF TestDefinedSetOp(#) = ({"a", "b"} # {"b", "c"})
       THEN Print("Test 86 OK", TRUE)
       ELSE Assert(FALSE, "Test 86 Failed")
  /\ IF TestDefinedSetOp(/=) = ({"a", "b"} /= {"b", "c"})
       THEN Print("Test 87 OK", TRUE)
       ELSE Assert(FALSE, "Test 87 Failed")
  /\ IF TestIn(\in) = ("a"\in {"b", "c"})
       THEN Print("Test 88 OK", TRUE)
       ELSE Assert(FALSE, "Test 88 Failed")
  /\ IF TestIn(\notin) = ("a" \notin {"b", "c"})
       THEN Print("Test 89 OK", TRUE)
       ELSE Assert(FALSE, "Test 89 Failed")
  /\ IF TestDefinedSetOp(\subseteq) = ({"a", "b"} \subseteq {"b", "c"})
       THEN Print("Test 90 OK", TRUE)
       ELSE Assert(FALSE, "Test 90 Failed")
  /\ IF TestDefinedSetOp(\) = ({"a", "b"} \ {"b", "c"})
       THEN Print("Test 91 OK", TRUE)
       ELSE Assert(FALSE, "Test 91 Failed")
  /\ IF TestDefinedSetOp(\cap) = ({"a", "b"} \cap {"b", "c"})
       THEN Print("Test 92 OK", TRUE)
       ELSE Assert(FALSE, "Test 92 Failed")
  /\ IF TestDefinedSetOp(\intersect) = ({"a", "b"} \intersect {"b", "c"})
       THEN Print("Test 93 OK", TRUE)
       ELSE Assert(FALSE, "Test 93 Failed")
  /\ IF TestDefinedSetOp(\cup) = ({"a", "b"} \cup {"b", "c"})
       THEN Print("Test 94 OK", TRUE)
       ELSE Assert(FALSE, "Test 94 Failed")
  /\ IF TestDefinedSetOp(\union) = ({"a", "b"} \union {"b", "c"})
       THEN Print("Test 95 OK", TRUE)
       ELSE Assert(FALSE, "Test 95 Failed")


==============================================================
78
ALL UNDEFINED INFIX OPERATORS

+ 
- 
* 
/ 
..
< 
> 
\leq 
=<
<=
\geq 
>=
% 
^
\circ 
\o
++ 
\div 
...
-- 
\oplus 
(+)
\ominus 
(-)
\otimes 
(\X)
\oslash 
(/)
\odot 
(.)
** 
\sqcap 
// 
\prec 
\succ 
\preceq 
\succeq 
\sqcup 
^^
\ll 
\gg 
<: 
& 
&& 
\sqsubset 
\sqsupset 
\sqsubseteq 
\sqsupseteq 
| 
|| 
\subset 
\supset 
\supseteq 
\star 
%% 
|- 
-|
|= 
=|
\bullet 
##
\sim 
\simeq 
\approx 
\cong 
$
$$
:= 
::= 
\asymp 
\doteq 
?? 
!! 
\propto 
\wr 
\uplus 
\bigcirc 


BUILT-IN BOOLEANS
=>
\equiv
<=>
/\
\land
\/
\lor

BUILT-IN SET OPERATORS
#
/=
\in
\notin
\subseteq
\
\cap
\intersect
\cup
\union

OTHER

-+->
~>
\cdot
