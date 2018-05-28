---------------------------- MODULE test216a ------------------------
EXTENDS Naturals
CONSTANT D

ASSUME Ass2 == D + 0 = 42 
THEOREM Thm2 == D + 0 = 42
Thm2Def == D + 0 = 42

INSTANCE test216b WITH E <- D, y <- 0   
  \* 12 June 2014: Changed from Test216b, which is now illegal
I == INSTANCE test216b WITH E <- D, y <- 0
  \* 12 June 2014: Changed from Test216b, which is now illegal


====================================================================
