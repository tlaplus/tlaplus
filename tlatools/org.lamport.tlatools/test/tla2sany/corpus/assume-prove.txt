===============================|||
Basic Assume/Prove
===============================|||

---- MODULE Test ----
THEOREM thm ==
  ASSUME P, Q
  PROVE C
OBVIOUS
====

-------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (theorem
    name: (identifier) (def_eq)
    statement: (assume_prove
      assumption: (identifier_ref)
      assumption: (identifier_ref)
      conclusion: (identifier_ref)
    )
    proof: (terminal_proof)
  )
(double_line)))

===============================|||
Nested Assume/Prove With Label
===============================|||

---- MODULE Test ----
THEOREM thm ==
  ASSUME asm :: 
    ASSUME P
    PROVE Q
  PROVE C
OMITTED
====

-------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (theorem
    name: (identifier) (def_eq)
    statement: (assume_prove
      assumption: (inner_assume_prove
        (identifier) (label_as)
        (assume_prove
          assumption: (identifier_ref)
          conclusion: (identifier_ref)
        )
      )
      conclusion: (identifier_ref)
    )
    proof: (terminal_proof)
  )
(double_line)))

===============================|||
Assume/Prove With New Constant
===============================|||

---- MODULE Test ----
THEOREM thm ==
  ASSUME NEW CONSTANT x \in S
  PROVE C
OBVIOUS
====

-------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (theorem
    name: (identifier) (def_eq)
    statement: (assume_prove
      assumption: (new (statement_level) (identifier) (set_in) (identifier_ref))
      conclusion: (identifier_ref)
    )
    proof: (terminal_proof)
  )
(double_line)))

===============================|||
Assume/Prove With New Operator
===============================|||

---- MODULE Test ----
THEOREM thm ==
  ASSUME NEW TEMPORAL f(_, _)
  PROVE C
OMITTED
====

-------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (theorem
    name: (identifier) (def_eq)
    statement: (assume_prove
      assumption: (new (statement_level) (operator_declaration
        name: (identifier) parameter: (placeholder) parameter: (placeholder)
      ))
      conclusion: (identifier_ref)
    )
    proof: (terminal_proof)
  )
(double_line)))

===============================|||
Assume/Prove in Suffices Step
===============================|||

---- MODULE Test ----
THEOREM TRUE
<1>a. SUFFICES
  ASSUME CONSTANT x \in S
  PROVE TRUE
<1>b. QED
====

-------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (theorem statement: (boolean)
    proof: (non_terminal_proof
      (proof_step (proof_step_id (level) (name))
        (suffices_proof_step (assume_prove
          assumption: (new (statement_level) (identifier) (set_in) (identifier_ref))
          conclusion: (boolean)
        ))
      )
      (qed_step (proof_step_id (level) (name)))
    )
  )
(double_line)))

===============================|||
Assume/Prove with Mixed Assumptions
===============================|||

---- MODULE Test ----
THEOREM thm ==
  ASSUME
    NEW f,
    1 + 2,
    /\ 1
    /\ 2,
    lbl :: ASSUME P PROVE Q
  PROVE C
OMITTED
====

-------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (theorem
    name: (identifier) (def_eq)
    statement: (assume_prove
      assumption: (new (identifier))
      assumption: (bound_infix_op lhs: (nat_number) symbol: (plus) rhs: (nat_number))
      assumption: (conj_list (conj_item (bullet_conj) (nat_number)) (conj_item (bullet_conj) (nat_number)))
      assumption: (inner_assume_prove
        (identifier)
        (label_as)
        (assume_prove
          assumption: (identifier_ref)
          conclusion: (identifier_ref)
        )
      )
      conclusion: (identifier_ref)
    )
    proof: (terminal_proof)
  )
(double_line)))

