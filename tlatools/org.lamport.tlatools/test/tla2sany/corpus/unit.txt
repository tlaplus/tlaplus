=============|||
VARIABLE Declaration
=============|||

---- MODULE Test ----
VARIABLE a, b, c
VARIABLES x, y, z
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (variable_declaration (identifier) (identifier) (identifier))
  (variable_declaration (identifier) (identifier) (identifier))
(double_line)))

=============|||
CONSTANT Declaration
=============|||

---- MODULE Test ----
CONSTANT x, y, z
CONSTANTS f(_, _), _+_, -._, _^+
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (constant_declaration (identifier) (identifier) (identifier))
  (constant_declaration
    (operator_declaration (identifier) (placeholder) (placeholder))
    (operator_declaration (placeholder) (infix_op_symbol (plus)) (placeholder))
    (operator_declaration (prefix_op_symbol (negative)) (placeholder))
    (operator_declaration (placeholder) (postfix_op_symbol (sup_plus)))
  )
(double_line)))

=============|||
Basic Operator Definition
=============|||

---- MODULE Test ----
op == f(10)
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (bound_op name: (identifier_ref) parameter: (nat_number))
  )
(double_line)))

===============================|||
INSTANCE With Jlist Substitutions
===============================|||

---- MODULE Test ----
INSTANCE M WITH
  A <- /\ 1,
  B <- /\ 2,
  C <- /\ \/ 3
          \/ 4,
  D <- \/ 5
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (instance (identifier_ref)
    (substitution (identifier_ref) (gets)
      (conj_list (conj_item (bullet_conj) (nat_number)))
    )
    (substitution (identifier_ref) (gets)
      (conj_list (conj_item (bullet_conj) (nat_number)))
    )
    (substitution (identifier_ref) (gets)
      (conj_list (conj_item (bullet_conj)
        (disj_list
          (disj_item (bullet_disj) (nat_number))
          (disj_item (bullet_disj) (nat_number))
        )
      ))
    )
    (substitution (identifier_ref) (gets)
      (disj_list (disj_item (bullet_disj) (nat_number)))
    )
  )
(double_line)))

===============================|||
INSTANCE With Operator Substitutions
===============================|||

---- MODULE Test ----
INSTANCE M WITH
  A <- a,
  SUBSET <- b,
  * <- c,
  ' <- d
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (instance (identifier_ref)
    (substitution (identifier_ref) (gets) (identifier_ref))
    (substitution (prefix_op_symbol (powerset)) (gets) (identifier_ref))
    (substitution (infix_op_symbol (mul)) (gets) (identifier_ref))
    (substitution (postfix_op_symbol (prime)) (gets) (identifier_ref))
  )
(double_line)))

