---- MODULE NestedModuleLetInstance ----
---- MODULE LetInner ----
foo == 42
====
op == LET Inst == INSTANCE LetInner IN Inst!foo
====
