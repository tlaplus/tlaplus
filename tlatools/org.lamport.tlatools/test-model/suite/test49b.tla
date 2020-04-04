--------------- MODULE test49b -------------

(* test definability of operators with aliases *)


EXTENDS TLC

VARIABLE x

u \oplus v == u
u \ominus v == u
u \odot v == u
u \oslash v == u
u \otimes v == u 
u \circ v == u
u \mod v == u
u =<  v == u
u >= v == u


Init == 
 /\ x = 0
 /\ Print("******************************************************", TRUE)
 /\ Print("Several tests have been commented out because of bugs.", TRUE)
 /\ Print("******************************************************", TRUE)

Next ==
   /\ x = 0
   /\ 
      \/ x' = x \oplus 1  
      \/ x' = x \ominus 1  
      \/ x' = x \odot 1  
      \/ x' = x \oslash 1  
      \/ x' = x \otimes 1 
\*      \/ x' = x \circ 1 
\*      \/ x' = x \mod 1   \* causes TLC bug
\*      \/ x' = (x =<  1)  \* causes TLC bug 
\*      \/ x' = (x >= 1 )  \* causes TLC bug 
=======================================
