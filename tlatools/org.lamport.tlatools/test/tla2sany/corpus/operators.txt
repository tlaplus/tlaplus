=============|||
Lexically-Conflicting Nonfix Operators
=============|||

---- MODULE Test ----
conflicts_with_octal == \o (1,2)
====

--------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_nonfix_op (infix_op_symbol (circ)) (nat_number) (nat_number))
  )
(double_line)))

=============|||
Minus and Negative
=============|||

---- MODULE Test ----
op == -. (1)
op == - (1)
op == - 1 - 2
====

--------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_nonfix_op (prefix_op_symbol (negative)) (nat_number))
  )
  (operator_definition (identifier) (def_eq)
    (bound_prefix_op (negative) (parentheses (nat_number)))
  )
  (operator_definition (identifier) (def_eq)
    (bound_infix_op (bound_prefix_op (negative) (nat_number)) (minus) (nat_number))
  )
(double_line)))

=============|||
Higher-Order Operator Parameter Declarations
=============|||

---- MODULE Test ----
f(x, g(_, _), _+_, -._, _^+) == x
====

--------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier)
    (identifier)
    (operator_declaration (identifier) (placeholder) (placeholder))
    (operator_declaration (placeholder) (infix_op_symbol (plus)) (placeholder))
    (operator_declaration (prefix_op_symbol (negative)) (placeholder))
    (operator_declaration (placeholder) (postfix_op_symbol (sup_plus)))
  (def_eq) (identifier_ref))
(double_line)))

=============|||
LAMBDA Parameter
=============|||

---- MODULE Test ----
op == f(LAMBDA x, y : x + y, LAMBDA x : 0)
====

--------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq) definition:
    (bound_op name: (identifier_ref)
      parameter: (lambda (identifier) (identifier) (bound_infix_op lhs: (identifier_ref) symbol: (plus) rhs: (identifier_ref)))
      parameter: (lambda (identifier) (nat_number))
    )
  )
(double_line)))

