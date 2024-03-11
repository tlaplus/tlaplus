=============|||
Basic Label
=============|||

---- MODULE Test ----
op(x) == lbl :: x
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) parameter: (identifier) (def_eq)
    definition: (label name: (identifier) (label_as) expression: (identifier_ref))
  )
(double_line)))

=============|||
Label With Parameters
=============|||

---- MODULE Test ----
op == \A a, b \in Nat : lbl(a, b) :: P(a, b)
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (bounded_quantification
      quantifier: (forall)
      bound: (quantifier_bound intro: (identifier) intro: (identifier) (set_in) set: (nat_number_set))
      expression: (label
        name: (identifier) parameter: (identifier_ref) parameter: (identifier_ref)
        (label_as)
        expression: (bound_op name: (identifier_ref) parameter: (identifier_ref) parameter: (identifier_ref))
      )
    )
  )
(double_line)))

