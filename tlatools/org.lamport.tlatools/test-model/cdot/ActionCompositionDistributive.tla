------ MODULE ActionCompositionDistributive ------

VARIABLE x, y, z
vars == <<x, y, z>>

HL == INSTANCE HL 
      WITH x <- z, 
           y <- z

Init ==
    /\ z = 1
    \* This should rather be HL!Init, but TLC won't accept it:
    \*  Error: current state is not a legal state
    \*  While working on the initial state:
    \*  /\ x = null
    \*  /\ y = null
    \*  /\ z = 0
    /\ x = 0
    /\ y = 0

--------------------------

ASpec == 
	Init /\ [][HL!Next /\ z' \in {0,1,2}]_vars

--------------------------

BSpec == 
	Init /\ [][(HL!A \cdot HL!B) /\ z' \in {0,1,2}]_vars

==========================

-------- MODULE HL -------
EXTENDS Naturals

VARIABLE x, y

Init ==
    /\ x = 0
    /\ y = 0

A ==
    /\ y' = x + 1
    /\ x' = x   \* With UNCHANGED x, TLC would warn about z being changed.

B ==
    /\ x  # y
    /\ y' = x
    /\ x' = x   \* With UNCHANGED x, TLC would warn about z being changed.

Next ==
    A \cdot B

Spec ==
    Init /\ [][Next]_<<x,y>>

==========================


LL:

A classic example is in a spec that implies x and y are numbers, where

A == (x' = x) /\ (y' = x + 1)

B == (x  # y) /\ (x' = x) /\ (y' = x)

Then

Aspec: ((A \cdot B) WITH x <- z, y <- z) equals z'=z

Bspec: (A WITH x <- z, y <- z) \cdot (B WITH x <- z, y <- z) equals FALSE

This is the classic example of an action A showing that instantiation doesn't distribute over ENABLED.

----------------------------------------------------------------------------

"For each subexpression of the form B \cdot C, replace each primed occurrence of x in B
and each unprimed occurrence of x in C by a new symbol $x that is different from any
identifier and from any other symbol that occurs in B or C."

(Section 17.8 "The semantics of instantiation" on page 338 of Specifying Systems)


Aspec:

    (x' = x /\ y' = x + 1) \cdot ( x #  y /\ x' =  x /\ y' =  x)
    
  Apply the above replacement rule (\cdot):

    ($x = x /\ $y = x + 1) \cdot ($x # $y /\ x' = $x /\ y' = $x)

  Apply substitution (WITH):

    ($x = z /\ $y = z + 1) \cdot ($x # $y /\ z' = $x /\ z' = $x)

  Thus:
    z = z'

BSpec:

    (x' = x /\ y' = x + 1) \cdot ( x #  y /\ x' =  x /\ y' =  x)

  Apply substitution (WITH):

    (...) \cdot (z # z /\ ...)

  Thus:
    FALSE (Contradiction)
    
----------------------------------------------------------------------------
    
More test cases:
- Reverse A \cdot B to B \cdot A
- \cdot nested within another \cdot
- \cdot nested within ENABLED
- ENABLED nested within \cdot
- priming of any state-level expression such as terminated' where terminated == var1 \in ... /\ var2 = ...

    