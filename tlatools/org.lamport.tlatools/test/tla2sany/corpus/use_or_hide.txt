=============|||
Use & Hide Declarations
=============|||

---- MODULE Test ----
USE x, MODULE M, 1 + 3
HIDE DEFS MODULE M, -., *, ^+
USE x, MODULE M DEF MODULE M, x
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (use_or_hide (use_body
    (use_body_expr
      (identifier_ref)
      (module_ref (identifier_ref))
      (bound_infix_op lhs: (nat_number) symbol: (plus) rhs: (nat_number))
    )
  ))
  (use_or_hide (use_body
    (use_body_def
      (module_ref (identifier_ref))
      (prefix_op_symbol (negative))
      (infix_op_symbol (mul))
      (postfix_op_symbol (sup_plus))
    )
  ))
  (use_or_hide (use_body
    (use_body_expr
      (identifier_ref)
      (module_ref (identifier_ref))
    )
    (use_body_def
      (module_ref (identifier_ref))
      (identifier_ref)
    )
  ))
(double_line)))

