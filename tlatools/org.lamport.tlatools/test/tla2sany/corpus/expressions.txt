==============================|||
Nested Parentheses
==============================|||

---- MODULE Test ----
op == ((((x))))
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (parentheses (parentheses (parentheses (parentheses (identifier_ref)))))
  )
(double_line)))

==============================|||
Tuple Literal
==============================|||

---- MODULE Test ----
op == <<a, <<b, c>>>>
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (tuple_literal
      (langle_bracket)
      (identifier_ref)
      (tuple_literal
        (langle_bracket)
        (identifier_ref)
        (identifier_ref)
        (rangle_bracket)
      )
      (rangle_bracket)
    )
  )
(double_line)))

======================|||
Tuple Literal with Jlist
======================|||

---- MODULE Test ----
op == <<
  /\ 1
  /\ 2
    >>
  /\ 3
====

----------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (bound_infix_op
      lhs: (tuple_literal
        (langle_bracket)
        (conj_list
          (conj_item (bullet_conj) (nat_number))
          (conj_item (bullet_conj) (nat_number))
        )
        (rangle_bracket)
      )
      symbol: (land)
      rhs: (nat_number)
    )
  )
(double_line)))

