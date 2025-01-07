---------------------------- MODULE Github1109a ---------------------------
EXTENDS Sequences

CONSTANTS C

VARIABLE x

C2 == x \* References variable, so C2 is non-constant.

Init == x = C

Next == UNCHANGED x
==========================================================================
---------------------------- CONFIG Github1109a ---------------------------
CONSTANT C <- C2
INIT Init
NEXT Next
==========================================================================
