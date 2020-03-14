--------------- MODULE test49a -------------

(* test definability of operators with aliases *)


EXTENDS TLC

VARIABLE x

u (+) v == u
u (-) v == u
u (.) v == u
u (/) v == u
u (\X) v == u \* parser can't cope with this
u \o v == u
u % v == u
u \leq  v == u
u \geq v == u


Init == 
 /\ x = 0
 /\ Print("******************************************************", TRUE)
 /\ Print("Several tests have been commented out because of bugs.", TRUE)
 /\ Print("******************************************************", TRUE)

Next ==
   /\ x = 0
   /\ 
      \/ x' = x (+) 1    \* caused TLC bug
      \/ x' = x (-) 1    \* caused TLC bug
      \/ x' = x (.) 1    \* caused TLC bug
      \/ x' = x (/) 1    \* caused TLC bug
      \/ x' = x (\X) 1   \* parser can't cope with this.
      \/ x' = x \o 1 
      \/ x' = x % 1 
      \/ x' = (x \leq  1) 
      \/ x' = (x \geq 1 ) 
=======================================
