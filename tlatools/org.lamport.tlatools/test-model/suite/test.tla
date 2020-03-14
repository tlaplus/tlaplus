------------- MODULE Foo  --------------
EXTENDS Naturals

Foo == \A x \in {1} : lab(x) :: x = 1

Bar == Foo!lab(1)

ASSUME Bar
=============================================
