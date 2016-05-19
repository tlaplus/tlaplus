------- MODULE test47 -----

\* Checks EXTENDing of both Naturals and Integers

EXTENDS test47a , Integers 

Init == x = -1

Next == x'= IF x = -3 THEN x ELSE x - 1

Inv == TRUE
==========================
