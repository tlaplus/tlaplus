--------------------------- MODULE ParamInstance ---------------------------
EXTENDS Naturals

VARIABLE value

  ---------- MODULE Ring ----------
  VARIABLE cardinality
  
  Init == /\ cardinality > 1
          /\ value \in (0 .. (cardinality - 1))
          
  Next == value' = (value + 1) % cardinality
  
  Spec == /\ Init
          /\ [][Next]_<<value, cardinality>>
          
  x $$ y == (x + y) % cardinality
  =================================
  
Z7(cardinality) == INSTANCE Ring

\* Parameterized instance invoking custom infix operator
ModSanityCheck == Z7(7)!$$(5,9) < 7

\* Referencing a single parameterized instance's definition
SpecA == Z7(7)!Spec

\* A conjunction of the parameterized instance's definition
\*		as well as the custom infix usage and weak fairness
SpecB == /\ Z7(7)!Init
         /\ [][Z7(7)!Next]_value
         /\ WF_value(Z7(7)!Next)
         /\ ModSanityCheck


Init == Z7(7)!Init
Next == Z7(7)!Next


\* Failing cases:
\* We cannot just negate ModSanityCheck because that is no longer a
\*		"trivially false" error message, rather it just prevents
\*		state generation. This should probably be considered a bug.
ModInsanityCheck == Z7(7)!$$(5,9) > 7
SpecC == Z7(7)!Spec /\ ModInsanityCheck
=============================================================================
