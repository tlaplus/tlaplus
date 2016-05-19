--------------- MODULE test49c -------------

(* test definability of operators with aliases *)


EXTENDS TLC

VARIABLE x

u \oplus v == u
u \ominus v == u
u \odot v == u
u \oslash v == u
u \otimes v == u 
u \o v == u
u \mod v == u
u =<  v == u
u >= v == u


Init == 
 /\ x = 0
 /\ Print("*************************************************************", TRUE)
 /\ Print("Almost all the tests have been commented out because of bugs.", TRUE)
 /\ Print("*************************************************************", TRUE)

Next ==
   /\ x = 0
   /\ 
\*      \/ x' = x (+) 1     \* causes TLC bug
\*      \/ x' = x (-) 1     \* causes TLC bug
\*      \/ x' = x (.) 1     \* causes TLC bug
\*      \/ x' = x (/) 1     \* causes TLC bug
\*      \/ x' = x (\X) 1  \* parser can't handle this
\*      \/ x' = x \circ 1   \* causes TLC bug
      \/ x' = x % 1   
\*      \/ x' = (x =<  1)  \* TLC bug : sets x' to TRUE
\*      \/ x' = (x >= 1 )    \* TLC bug : sets x' to FALSE
=======================================
