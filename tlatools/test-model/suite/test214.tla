------------------------------ MODULE test214 ------------------------------ 
\* Test that USE and HIDE cannot contain arbitrary expressions as 
\* facts.

THEOREM bar == <<1, 2>>

USE bar, bar!1 (*ERROR*)
         

HIDE bar, TRUE (*ERROR*)

THEOREM xx == ASSUME TRUE PROVE FALSE 
 <1>2. USE TRUE (*ERROR*), bar , xx , xx!1 (*ERROR*)
 <1>3. QED

=============================================================================
