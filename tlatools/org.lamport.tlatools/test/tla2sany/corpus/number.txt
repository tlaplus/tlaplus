======================|||
All Number Formats
======================|||

---- MODULE Test ----
op == 12345
op == 12345.12345
op == \b01010101
op == \B10101010
op == \o01234567
op == \O76543210
op == \h0123456789abcdef
op == \H9876543210FEDCBA
====

----------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq) (nat_number))
  (operator_definition (identifier) (def_eq) (real_number))
  (operator_definition (identifier) (def_eq) (binary_number (format) (value)))
  (operator_definition (identifier) (def_eq) (binary_number (format) (value)))
  (operator_definition (identifier) (def_eq) (octal_number (format) (value)))
  (operator_definition (identifier) (def_eq) (octal_number (format) (value)))
  (operator_definition (identifier) (def_eq) (hex_number (format) (value)))
  (operator_definition (identifier) (def_eq) (hex_number (format) (value)))
(double_line)))

======================|||
All Number Sets
======================|||

---- MODULE Test ----
op == Nat
op == Int
op == Real
====

----------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq) definition: (nat_number_set))
  (operator_definition name: (identifier) (def_eq) definition: (int_number_set))
  (operator_definition name: (identifier) (def_eq) definition: (real_number_set))
(double_line)))

