=============|||
Basic Recursive Declaration
=============|||

---- MODULE Test ----
RECURSIVE f(_)
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (recursive_declaration (operator_declaration (identifier) (placeholder)))
(double_line)))

=============|||
Recursive Declaration Without Parameters
=============|||

---- MODULE Test ----
RECURSIVE f
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (recursive_declaration (identifier))
(double_line)))

=============|||
Multiple Recursive Declarations
=============|||

---- MODULE Test ----
RECURSIVE f(_), g(_)
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (recursive_declaration
    (operator_declaration (identifier) (placeholder))
    (operator_declaration (identifier) (placeholder))
  )
(double_line)))

=============|||
Mixed Recursive Declarations
=============|||

---- MODULE Test ----
RECURSIVE f(_), g, h(_, _, _), _+_, -. _, _ ^+
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (recursive_declaration
    (operator_declaration (identifier) (placeholder))
    (identifier)
    (operator_declaration (identifier) (placeholder) (placeholder) (placeholder))
    (operator_declaration (placeholder) (infix_op_symbol (plus)) (placeholder))
    (operator_declaration (prefix_op_symbol (negative)) (placeholder))
    (operator_declaration (placeholder) (postfix_op_symbol (sup_plus)))
  )
(double_line)))

