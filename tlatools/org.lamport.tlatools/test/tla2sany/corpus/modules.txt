=============|||
Single module
=============|||

---- MODULE Test ----
====

-------------|||

(source_file
  (module (header_line) (identifier) (header_line) (double_line))
)

=============|||
Module with EXTENDS
=============|||

---- MODULE Test ----
EXTENDS M1, M2, M3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (extends (identifier_ref) (identifier_ref) (identifier_ref))
(double_line)))

=============|||
Nested modules
=============|||

---- MODULE Test ----
---- MODULE Inner ----
====
====

-------------|||

(source_file
  (module (header_line) (identifier) (header_line)
    (module (header_line) (identifier) (header_line) (double_line))
  (double_line))
)

=============|||
Multiple Nested modules
=============|||

---- MODULE Test ----
---- MODULE Inner ----
====
---- MODULE Inner2 ----
====
====

-------------|||

(source_file
  (module (header_line) (identifier) (header_line)
    (module (header_line) (identifier) (header_line) (double_line))
    (module (header_line) (identifier) (header_line) (double_line))
  (double_line))
)

