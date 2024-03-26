======================|||
Set Map
======================|||

---- MODULE Test ----
op ≜ {f(x) : x ∈ ℕ}
====

----------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (set_map
      map: (bound_op name: (identifier_ref) parameter: (identifier_ref))
      generator: (quantifier_bound intro: (identifier) (set_in) set: (nat_number_set))
    )
  )
(double_line)))

======================|||
Set Map with Multiple Generators
======================|||

---- MODULE Test ----
op ≜ {f(x, y, z) : x ∈ ℤ, y, z ∈ ℝ}
====

----------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (set_map
      map: (bound_op name: (identifier_ref) parameter: (identifier_ref) parameter: (identifier_ref) parameter: (identifier_ref))
      generator: (quantifier_bound intro: (identifier) (set_in) set: (int_number_set))
      generator: (quantifier_bound intro: (identifier) intro: (identifier) (set_in) set: (real_number_set))
    )
  )
(double_line)))


======================|||
Set Filter
======================|||

---- MODULE Test ----
op ≜ {x ∈ ℕ : P(x)}
====

----------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (set_filter
      generator: (quantifier_bound intro: (identifier) (set_in) set: (nat_number_set))
      filter: (bound_op name: (identifier_ref) parameter: (identifier_ref))
    )
  )
(double_line)))

======================|||
Set Filter with Tuple
======================|||

---- MODULE Test ----
op ≜ {⟨x, y, z⟩ ∈ ℕ × ℤ × ℝ : P(x, y, z)}
====

----------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (set_filter
      generator: (quantifier_bound
        intro: (tuple_of_identifiers (langle_bracket) (identifier) (identifier) (identifier) (rangle_bracket))
        (set_in)
        set: (bound_infix_op
          lhs: (bound_infix_op
            lhs: (nat_number_set)
            symbol: (times)
            rhs: (int_number_set)
          )
          symbol: (times)
          rhs: (real_number_set)
        )
      )
      filter: (bound_op name: (identifier_ref) parameter: (identifier_ref) parameter: (identifier_ref) parameter: (identifier_ref))
    )
  )
(double_line)))

=====================|||
Set Filter Precedence
=====================|||

---- MODULE Test ----
op ≜ {x ∈ S : x ∈ T}
====

---------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (set_filter
      generator: (quantifier_bound
        intro: (identifier) (set_in) set: (identifier_ref)
      )
      filter: (bound_infix_op
        lhs: (identifier_ref) symbol: (in) rhs: (identifier_ref)
      )
    )
  )
(double_line)))

======================|||
Set Filter with Jlist
======================|||

---- MODULE Test ----
op ≜ {
  x ∈
    ∧ A
    ∧ B
    ∧ C
      :
    ∧ D
    ∧ E
    ∧ F
}
====

----------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (set_filter
      (quantifier_bound
        (identifier) (set_in)
        (conj_list
          (conj_item (bullet_conj) (identifier_ref))
          (conj_item (bullet_conj) (identifier_ref))
          (conj_item (bullet_conj) (identifier_ref))
        )
      )
      (conj_list
        (conj_item (bullet_conj) (identifier_ref))
        (conj_item (bullet_conj) (identifier_ref))
        (conj_item (bullet_conj) (identifier_ref))
      )
    )
  )
(double_line)))

