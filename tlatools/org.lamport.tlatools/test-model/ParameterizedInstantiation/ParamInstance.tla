--------------------------- MODULE ParamInstance ---------------------------
EXTENDS Naturals

VARIABLE value

  ------ MODULE Ring ------
  VARIABLE cardinality
  
  Init == /\ cardinality > 1
          /\ value \in (0 .. cardinality)
          
  Next == value' = value % cardinality
             
  Spec == /\ Init
          /\ [][Next]_<<value, cardinality>>
  
  =================================
  
Z7(cardinality) == INSTANCE Ring

SpecA == Z7(7)!Spec
SpecB == /\ Z7(7)!Init
         /\ [][Z7(7)!Next]_<<value>>

Init == Z7(7)!Init
Next == Z7(7)!Next

=============================================================================
\* Modification History
\* Last modified Thu Apr 09 16:46:46 PDT 2020 by loki
\* Created Thu Apr 09 13:48:27 PDT 2020 by loki
