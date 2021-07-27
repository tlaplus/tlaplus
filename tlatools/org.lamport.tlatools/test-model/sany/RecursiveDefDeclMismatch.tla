------------------------- MODULE RecursiveDefDeclMismatch -------------------

RECURSIVE CountDown(_,_)
CountDown(n) == IF n = 0 THEN TRUE ELSE CountDown(n - 1)

=============================================================================
