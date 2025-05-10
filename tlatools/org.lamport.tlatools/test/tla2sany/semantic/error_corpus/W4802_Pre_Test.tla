If a symbol is defined then a record is defined with a field name
overlapping with the symbol, generate a warning since the value of
the symbol will not be used as the record field name.
---- MODULE W4802_Pre_Test ----
Foo == TRUE
SomeRecord == [Foo |-> 42]
====

