\* Copyright (c) 2025, Oracle and/or its affiliates.
---- MODULE Github1145 ----

EXTENDS Naturals, Sequences

F(seq) == SubSeq(seq, 2, 2)

ASSUME F([[i \in 1..4 |-> 0] EXCEPT ![2] = 1])[1]
     = F(<<0, 1, 0, 0>>                      )[1]

ASSUME F([[i \in {1, 2, 3, 4} |-> 0] EXCEPT ![2] = 1])[1]
     = F(<<0, 1, 0, 0>>                              )[1]

====
