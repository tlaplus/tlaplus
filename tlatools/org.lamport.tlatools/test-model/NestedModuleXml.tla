---- MODULE NestedModuleXml ----
op ==
  /\ TRUE
  /\ FALSE
      ---- MODULE Nested ----
      Foo == 42
      ====
====
