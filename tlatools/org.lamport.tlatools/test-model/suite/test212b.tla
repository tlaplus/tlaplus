-------------------------- MODULE test212b -------------------------
VARIABLE y
NoArg == y'
Leibniz(a4) == <<a4, y>>
Leibniz2(a44, a45) == <<a44, a45, y>>
NonLeibniz(a5) == ENABLED a5
NonLeibniz2(a6, a7) == {a6', a7}

=============================================================================
