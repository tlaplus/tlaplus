---- MODULE UndeclaredRecursion ----
EXTENDS Base, Integers

DefIsOdd(n) ==
	IF n = 0
	THEN FALSE
	ELSE IsEven(n-1)

=====
----- MODULE Base -----
EXTENDS Naturals

CONSTANT IsOdd(_)

IsEven(n) ==
	IF n = 0
	THEN TRUE
	ELSE IsOdd(n-1)

ASSUME IsEven(2)

====
---- CONFIG UndeclaredRecursion ----
CONSTANT IsOdd <- DefIsOdd
====