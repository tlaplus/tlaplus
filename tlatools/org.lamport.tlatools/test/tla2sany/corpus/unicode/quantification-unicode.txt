==============================|||
Bounded Quantification
==============================|||

---- MODULE Test ----
op ≜ ∀ x, y ∈ Nat, z ∈ Int, ⟨a, b, c⟩ ∈ Real : FALSE
op ≜ ∃ ⟨x, y⟩ ∈ Nat, a, b ∈ Int : TRUE
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (bounded_quantification
      quantifier: (forall)
      bound: (quantifier_bound
        intro: (identifier) intro: (identifier)
        (set_in)
        set: (nat_number_set)
      )
      bound: (quantifier_bound
        intro: (identifier)
        (set_in)
        set: (int_number_set)
      )
      bound: (quantifier_bound
        intro: (tuple_of_identifiers (langle_bracket) (identifier) (identifier) (identifier) (rangle_bracket))
        (set_in)
        set: (real_number_set)
      )
      expression: (boolean)
    )
  )
  (operator_definition name: (identifier) (def_eq)
    definition: (bounded_quantification
      quantifier: (exists)
      bound: (quantifier_bound
        intro: (tuple_of_identifiers (langle_bracket) (identifier) (identifier) (rangle_bracket))
        (set_in)
        set: (nat_number_set)
      )
      bound: (quantifier_bound
        intro: (identifier) intro: (identifier)
        (set_in)
        set: (int_number_set)
      )
      expression: (boolean)
    )
  )
(double_line)))

==============================|||
Unbounded Quantification
==============================|||

---- MODULE Test ----
op ≜ ∀ x : TRUE
op ≜ ∃ x, y : FALSE
op ≜ \AA x, y, z : TRUE
op ≜ \EE x, y, z, w : FALSE
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (unbounded_quantification
      quantifier: (forall)
      intro: (identifier)
      expression: (boolean)
    )
  )
  (operator_definition name: (identifier) (def_eq)
    definition: (unbounded_quantification
      quantifier: (exists)
      intro: (identifier)
      intro: (identifier)
      expression: (boolean)
    )
  )
  (operator_definition name: (identifier) (def_eq)
    definition: (unbounded_quantification
      quantifier: (temporal_forall)
      intro: (identifier)
      intro: (identifier)
      intro: (identifier)
      expression: (boolean)
    )
  )
  (operator_definition name: (identifier) (def_eq)
    definition: (unbounded_quantification
      quantifier: (temporal_exists)
      intro: (identifier)
      intro: (identifier)
      intro: (identifier)
      intro: (identifier)
      expression: (boolean)
    )
  )
(double_line)))

==============================|||
Bounded CHOOSE
==============================|||

---- MODULE Test ----
op ≜ CHOOSE x ∈ Nat : TRUE
op ≜ CHOOSE ⟨x, y, z⟩ ∈ S : FALSE
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (choose
      intro: (identifier)
      (set_in)
      set: (nat_number_set)
      expression: (boolean)
    )
  )
  (operator_definition name: (identifier) (def_eq)
    definition: (choose
      intro: (tuple_of_identifiers (langle_bracket) (identifier) (identifier) (identifier) (rangle_bracket))
      (set_in)
      set: (identifier_ref)
      expression: (boolean)
    )
  )
(double_line)))

==============================|||
Unbounded CHOOSE
==============================|||

---- MODULE Test ----
op ≜ CHOOSE x : TRUE
op ≜ CHOOSE ⟨x, y, z⟩ : FALSE
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (choose
      intro: (identifier)
      expression: (boolean)
    )
  )
  (operator_definition name: (identifier) (def_eq)
    definition: (choose
      intro: (tuple_of_identifiers (langle_bracket) (identifier) (identifier) (identifier) (rangle_bracket))
      expression: (boolean)
    )
  )
(double_line)))

