If a recursive operator is declared at one level of a LET/IN block, it must
be defined in that level and not in a nested level.
---- MODULE E2045_Test ----
op ==
  LET
    RECURSIVE recDef
    def ==
      LET recDef == 0
      IN 0
  IN 0
====

