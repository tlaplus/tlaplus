=============|||
Postfix Operator Definition
=============|||

---- MODULE Test ----

x^+ == 1
x^* == 2
x^# == 3
x' == 4

====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition parameter: (identifier) name: (postfix_op_symbol (sup_plus)) (def_eq) definition: (nat_number))
  (operator_definition parameter: (identifier) name: (postfix_op_symbol (asterisk)) (def_eq) definition: (nat_number))
  (operator_definition parameter: (identifier) name: (postfix_op_symbol (sup_hash)) (def_eq) definition: (nat_number))
  (operator_definition parameter: (identifier) name: (postfix_op_symbol (prime)) (def_eq) definition: (nat_number))
(double_line)))

=============|||
Postfix Operator Declaration as Parameter
=============|||

---- MODULE Test ----

op(
  _ ^+,
  _ ^*,
  _ ^#,
  _ '
) == 4

====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier)
    parameter: (operator_declaration (placeholder) name: (postfix_op_symbol (sup_plus)))
    parameter: (operator_declaration (placeholder) name: (postfix_op_symbol (asterisk)))
    parameter: (operator_declaration (placeholder) name: (postfix_op_symbol (sup_hash)))
    parameter: (operator_declaration (placeholder) name: (postfix_op_symbol (prime)))
    (def_eq)
    definition: (nat_number)
  )
(double_line)))

=============|||
Postfix Operator Application
=============|||

---- MODULE Test ----
op == {
  x^+,
  x^*,
  x^#,
  x'
}
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq) definition: (finite_set_literal
    (bound_postfix_op lhs: (identifier_ref) symbol: (sup_plus))
    (bound_postfix_op lhs: (identifier_ref) symbol: (asterisk))
    (bound_postfix_op lhs: (identifier_ref) symbol: (sup_hash))
    (bound_postfix_op lhs: (identifier_ref) symbol: (prime))
  ))
(double_line)))

=============|||
Postfix Operators as Parameters
=============|||

---- MODULE Test ----
op == f(
  ^+,
  ^*,
  ^#,
  '
)
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq) definition: (bound_op name: (identifier_ref)
    parameter: (postfix_op_symbol (sup_plus))
    parameter: (postfix_op_symbol (asterisk))
    parameter: (postfix_op_symbol (sup_hash))
    parameter: (postfix_op_symbol (prime))
  ))
(double_line)))

=============|||
Nonfix Postfix Operators
=============|||

---- MODULE Test ----
op == {
  A!B!^+(x),
  A!B!^*(x),
  A!B!^#(x),
  A!B!'(x)
}
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq) definition: (finite_set_literal
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (postfix_op_symbol (sup_plus)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (postfix_op_symbol (asterisk)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (postfix_op_symbol (sup_hash)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (postfix_op_symbol (prime)) (identifier_ref)))
  ))
(double_line)))

