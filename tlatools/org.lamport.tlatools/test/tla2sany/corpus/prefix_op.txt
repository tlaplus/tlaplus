=============|||
Prefix Operator Definition
=============|||

---- MODULE Test ----

~x == 1
\lnot x == 2
\neg x == 3
UNION x == 4
SUBSET x == 5
DOMAIN x == 6
-. x == 7
ENABLED x == 8
UNCHANGED x == 9
[] x == 10
<> x == 11

====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (prefix_op_symbol (lnot)) parameter: (identifier) (def_eq) definition: (nat_number))
  (operator_definition name: (prefix_op_symbol (lnot)) parameter: (identifier) (def_eq) definition: (nat_number))
  (operator_definition name: (prefix_op_symbol (lnot)) parameter: (identifier) (def_eq) definition: (nat_number))
  (operator_definition name: (prefix_op_symbol (union)) parameter: (identifier) (def_eq) definition: (nat_number))
  (operator_definition name: (prefix_op_symbol (powerset)) parameter: (identifier) (def_eq) definition: (nat_number))
  (operator_definition name: (prefix_op_symbol (domain)) parameter: (identifier) (def_eq) definition: (nat_number))
  (operator_definition name: (prefix_op_symbol (negative)) parameter: (identifier) (def_eq) definition: (nat_number))
  (operator_definition name: (prefix_op_symbol (enabled)) parameter: (identifier) (def_eq) definition: (nat_number))
  (operator_definition name: (prefix_op_symbol (unchanged)) parameter: (identifier) (def_eq) definition: (nat_number))
  (operator_definition name: (prefix_op_symbol (always)) parameter: (identifier) (def_eq) definition: (nat_number))
  (operator_definition name: (prefix_op_symbol (eventually)) parameter: (identifier) (def_eq) definition: (nat_number))
(double_line)))

=============|||
Prefix Operator Declaration as Parameter
=============|||

---- MODULE Test ----

op(
  ~ _,
  \lnot _,
  \neg _,
  UNION _,
  SUBSET _,
  DOMAIN _,
  -. _,
  ENABLED _,
  UNCHANGED _,
  [] _,
  <> _
) == 11

====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier)
    parameter: (operator_declaration name: (prefix_op_symbol (lnot)) (placeholder))
    parameter: (operator_declaration name: (prefix_op_symbol (lnot)) (placeholder))
    parameter: (operator_declaration name: (prefix_op_symbol (lnot)) (placeholder))
    parameter: (operator_declaration name: (prefix_op_symbol (union)) (placeholder))
    parameter: (operator_declaration name: (prefix_op_symbol (powerset)) (placeholder))
    parameter: (operator_declaration name: (prefix_op_symbol (domain)) (placeholder))
    parameter: (operator_declaration name: (prefix_op_symbol (negative)) (placeholder))
    parameter: (operator_declaration name: (prefix_op_symbol (enabled)) (placeholder))
    parameter: (operator_declaration name: (prefix_op_symbol (unchanged)) (placeholder))
    parameter: (operator_declaration name: (prefix_op_symbol (always)) (placeholder))
    parameter: (operator_declaration name: (prefix_op_symbol (eventually)) (placeholder))
    (def_eq)
    definition: (nat_number)
  )
(double_line)))

=============|||
Prefix Operator Application
=============|||

---- MODULE Test ----
op == {
  ~x,
  \lnot x,
  \neg x,
  UNION x,
  SUBSET x,
  DOMAIN x,
  -x,
  ENABLED x,
  UNCHANGED x,
  []x,
  <>x
}
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq) definition: (finite_set_literal
    (bound_prefix_op symbol: (lnot) rhs: (identifier_ref))
    (bound_prefix_op symbol: (lnot) rhs: (identifier_ref))
    (bound_prefix_op symbol: (lnot) rhs: (identifier_ref))
    (bound_prefix_op symbol: (union) rhs: (identifier_ref))
    (bound_prefix_op symbol: (powerset) rhs: (identifier_ref))
    (bound_prefix_op symbol: (domain) rhs: (identifier_ref))
    (bound_prefix_op symbol: (negative) rhs: (identifier_ref))
    (bound_prefix_op symbol: (enabled) rhs: (identifier_ref))
    (bound_prefix_op symbol: (unchanged) rhs: (identifier_ref))
    (bound_prefix_op symbol: (always) rhs: (identifier_ref))
    (bound_prefix_op symbol: (eventually) rhs: (identifier_ref))
  ))
(double_line)))

=============|||
Prefix Operator References
=============|||

---- MODULE Test ----
op == f(
  ~,
  \lnot,
  \neg,
  UNION,
  SUBSET,
  DOMAIN,
  -.,
  ENABLED,
  UNCHANGED,
  [],
  <>
)
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq) definition: (bound_op name: (identifier_ref)
    parameter: (prefix_op_symbol (lnot))
    parameter: (prefix_op_symbol (lnot))
    parameter: (prefix_op_symbol (lnot))
    parameter: (prefix_op_symbol (union))
    parameter: (prefix_op_symbol (powerset))
    parameter: (prefix_op_symbol (domain))
    parameter: (prefix_op_symbol (negative))
    parameter: (prefix_op_symbol (enabled))
    parameter: (prefix_op_symbol (unchanged))
    parameter: (prefix_op_symbol (always))
    parameter: (prefix_op_symbol (eventually))
  ))
(double_line)))

=============|||
Nonfix Prefix Operators
=============|||

---- MODULE Test ----
op == {
  A!B!~(x),
  A!B!\lnot(x),
  A!B!\neg(x),
  A!B!UNION(x),
  A!B!SUBSET(x),
  A!B!DOMAIN(x),
  A!B!-.(x),
  A!B!ENABLED(x),
  A!B!UNCHANGED(x),
  A!B![](x),
  A!B!<>(x)
}
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq) definition: (finite_set_literal
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (prefix_op_symbol (lnot)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (prefix_op_symbol (lnot)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (prefix_op_symbol (lnot)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (prefix_op_symbol (union)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (prefix_op_symbol (powerset)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (prefix_op_symbol (domain)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (prefix_op_symbol (negative)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (prefix_op_symbol (enabled)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (prefix_op_symbol (unchanged)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (prefix_op_symbol (always)) (identifier_ref)))
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (prefix_op_symbol (eventually)) (identifier_ref)))
  ))
(double_line)))

