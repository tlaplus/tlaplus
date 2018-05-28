--------------------------- MODULE test212 --------------------------
\* Test of Leibniz checking
\*   Uses the fact that you can't substitute a non-Leibniz operator
\*   for a constant operator.
VARIABLE x

Leibniz(a2) == {a2 , x'}
NonLeibniz2(a, b) == <<a, b'>>
L ==  INSTANCE test212b WITH y <- x

NonLeibniz(a1) == a1'
Leibniz2(a, b) == <<a, b, x'>>

I(a) == INSTANCE test212b WITH y <- a
LL == INSTANCE test212b WITH y <- ENABLED (x'=x)
NonL(a) ==INSTANCE test212b WITH y <- ENABLED a

\* Legal
L1 == INSTANCE test212a WITH Op <- Leibniz, Op2 <- Leibniz2
L2 == INSTANCE test212a WITH Op <- LAMBDA a : I(a)!Leibniz(1), 
                             Op2 <- Leibniz2
L3 == INSTANCE test212a WITH Op <- Leibniz, Op2 <- I!Leibniz
L4 == INSTANCE test212a WITH Op <- Leibniz, Op2 <- LL!Leibniz2
L5 == INSTANCE test212a WITH Op <- LL!Leibniz, Op2 <- Leibniz2

\* Illegal
I1 == INSTANCE test212a WITH Op <- Leibniz, Op2 <- NonLeibniz2
I2 == INSTANCE test212a WITH Op <- NonLeibniz, Op2 <- Leibniz2
I3 == INSTANCE test212a WITH Op <- NonL!NoArg, Op2 <- Leibniz2
I4 == INSTANCE test212a WITH Op <- Leibniz, Op2 <- L!NonLeibniz2
I5 == INSTANCE test212a WITH Op <- Leibniz, Op2 <- NonL!Leibniz
I6 == INSTANCE test212a WITH Op <- Leibniz, Op2 <- I!NonLeibniz
==================================================================