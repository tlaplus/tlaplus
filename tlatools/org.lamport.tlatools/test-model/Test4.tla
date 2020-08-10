---------- MODULE Test4 -----------
VARIABLE x

ASSUME TRUE = FALSE \* No, it's not!

Spec == x = 0 /\ [][UNCHANGED x]_x

==============================================
