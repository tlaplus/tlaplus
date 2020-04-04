--------------- MODULE test49 -------------

(* test definability of operators with aliases *)


EXTENDS TLC

VARIABLE x

u (+) v == u
u (-) v == u
u (.) v == u
u (/) v == u
u (\X) v == u 
u \o v == u
u % v == u
u \leq  v == u
u \geq v == u


Init == 
 /\ x = 0

Next ==
   /\ x = 0
   /\ 
      \/ x' = x (+) 1    
      \/ x' = x (-) 1    
      \/ x' = x (.) 1    
      \/ x' = x (/) 1    
      \/ x' = x (\X) 1   
      \/ x' = x \o 1 
      \/ x' = x % 1 
      \/ x' = (x \leq  1) 
      \/ x' = (x \geq 1 ) 
=======================================
