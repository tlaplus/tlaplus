---- MODULE TestMergeContextError ----
EXTENDS TestMergeContextError2, TestMergeContextError3
====
---- MODULE TestMergeContextError2 ----
op == TRUE
====
---- MODULE TestMergeContextError3 ----
CONSTANT op
====
