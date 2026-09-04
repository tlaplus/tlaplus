\* EXTENDS a module whose body contains a nested module, both at the top level
\* and from a module nested in this one. Neither makes that module a unit here.
---- MODULE NestedModuleXmlExtender ----
EXTENDS NestedModuleXmlBase

---- MODULE Borrower ----
EXTENDS NestedModuleXmlBase
BorrowerOp == BaseOp
====

ExtOp == BaseOp
====
