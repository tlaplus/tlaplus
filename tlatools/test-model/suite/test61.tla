-------------------- MODULE test61 --------------------
(***************************************************************************)
(* Test of parametrized INSTANCE                                            *)
(***************************************************************************)
\* Because of bug, it Handles JSpec but not ISpec

EXTENDS Naturals

VARIABLE y

IM(x) == INSTANCE test61a

ISpec == IM(y)!Spec

Invariant == y \in 0..4

JM == INSTANCE test61a WITH x <- y
JSpec == JM!Spec

========================================

