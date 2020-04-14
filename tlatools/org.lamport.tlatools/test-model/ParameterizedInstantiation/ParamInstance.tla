--------------------------- MODULE ParamInstance ---------------------------
EXTENDS Naturals

VARIABLE value

  ---------- MODULE Ring ----------
  VARIABLE cardinality
  
  Init == /\ cardinality > 1
          /\ value \in (0 .. (cardinality - 1))
          
  Next == value' = value % cardinality
             
  Spec == /\ Init
          /\ [][Next]_<<value, cardinality>>
          
  x $$ y == (x + y) % cardinality
  =================================
  
Z7(cardinality) == INSTANCE Ring


ModSanityCheck == Z7(7)!$$(5,9) < 7
SpecA == Z7(7)!Spec /\ ModSanityCheck
SpecB == /\ Z7(7)!Init
         /\ [][Z7(7)!Next]_<<value>>
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
