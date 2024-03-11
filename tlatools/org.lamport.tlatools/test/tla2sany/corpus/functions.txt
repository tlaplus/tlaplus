===============================|||
Function Definition
===============================|||

---- MODULE Test ----
f[x \in Nat] == x
f[x, y \in Nat] == x
f[x, y \in Nat, z \in Real] == x
====

-------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (function_definition
    name: (identifier)
    (quantifier_bound
      intro: (identifier)
      (set_in)
      set: (nat_number_set)
    )
    (def_eq)
    definition: (identifier_ref)
  )
  (function_definition
    name: (identifier)
    (quantifier_bound
      intro: (identifier)
      intro: (identifier)
      (set_in)
      set: (nat_number_set)
    )
    (def_eq)
    definition: (identifier_ref)
  )
  (function_definition
    name: (identifier)
    (quantifier_bound
      intro: (identifier)
      intro: (identifier)
      (set_in)
      set: (nat_number_set)
    )
    (quantifier_bound
      intro: (identifier)
      (set_in)
      set: (real_number_set)
    )
    (def_eq)
    definition: (identifier_ref)
  )
(double_line)))

===============================|||
Function Evaluation
===============================|||

---- MODULE Test ----
op == f[1,2,3]
====

-------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (function_evaluation (identifier_ref) (nat_number) (nat_number) (nat_number))
  )
(double_line)))

===============================|||
Jlist Inside Function Evaluation
===============================|||

---- MODULE Test ----
op ==
    /\ 1
    /\ f[
        \/ 2
        \/ 3,
        /\ 4
          ]
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj)
        (function_evaluation (identifier_ref)
          (disj_list
            (disj_item (bullet_disj) (nat_number))
            (disj_item (bullet_disj) (nat_number))
          )
          (conj_list (conj_item (bullet_conj) (nat_number)))
        )
      )
    )
  )
(double_line)))

===============================|||
Function Literal
===============================|||

---- MODULE Test ----
op == [n \in Nat |-> 2*n]
====

-------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (function_literal
      (quantifier_bound intro: (identifier) (set_in) set: (nat_number_set))
      (all_map_to)
      (bound_infix_op lhs: (nat_number) symbol: (mul) rhs: (identifier_ref))
    )
  )
(double_line)))

===============================|||
Function Literal with Multiple Parameters and Jlist
===============================|||

---- MODULE Test ----
op == [
  x, y \in Nat, <<a, b>> \in
    /\ A
    /\ B
      |->
        /\ A
        /\ B
            ]
====

-------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (function_literal
      (quantifier_bound intro: (identifier) intro: (identifier) (set_in) set: (nat_number_set))
      (quantifier_bound
        intro: (tuple_of_identifiers (langle_bracket) (identifier) (identifier) (rangle_bracket))
        (set_in)
        set: (conj_list
          (conj_item (bullet_conj) (identifier_ref))
          (conj_item (bullet_conj) (identifier_ref))
        )
      )
      (all_map_to)
      (conj_list
        (conj_item (bullet_conj) (identifier_ref))
        (conj_item (bullet_conj) (identifier_ref))
      )
    )
  )
(double_line)))

===============================|||
Function Set
===============================|||

---- MODULE Test ----
op == [Nat -> [Nat -> Real]]
====

-------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (set_of_functions
      (nat_number_set)
      (maps_to)
      (set_of_functions
        (nat_number_set)
        (maps_to)
        (real_number_set)
      )
    )
  )
(double_line)))

===============================|||
Jlist Inside Function Set
===============================|||

---- MODULE Test ----
op == [
  /\ A
  /\ B
  /\ C
    ->
      /\ D
      /\ E
      /\ F
        ]
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (set_of_functions
      (conj_list
        (conj_item (bullet_conj) (identifier_ref))
        (conj_item (bullet_conj) (identifier_ref))
        (conj_item (bullet_conj) (identifier_ref))
      )
      (maps_to)
      (conj_list
        (conj_item (bullet_conj) (identifier_ref))
        (conj_item (bullet_conj) (identifier_ref))
        (conj_item (bullet_conj) (identifier_ref))
      )
    )
  )
(double_line)))

