Label names cannot be duplicated where referring to the label would refer
to an ambiguous expression. Label names *can* be duplicated if they are
nested; for example, lbl :: lbl :: expr is not ambiguous because to address
expression you would use lbl!lbl instead of just lbl.
---- MODULE E2041_Test ----
op == {lbl :: 0, lbl :: 0}
====

