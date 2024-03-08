==============================|||
Record Literal
==============================|||

---- MODULE Test ----
op == [
  foo |-> 1,
  bar |-> 2,
  baz |-> 3
]
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (record_literal
      (identifier) (all_map_to) (nat_number)
      (identifier) (all_map_to) (nat_number)
      (identifier) (all_map_to) (nat_number)
    )
  )
(double_line)))

==============================|||
Record Literal with JList
==============================|||

---- MODULE Test ----
op == [
  foo |->
    /\ 1
    /\ 2,
      bar |->
        \/ 3
        \/ 4
]
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (record_literal
      (identifier) (all_map_to) (conj_list
        (conj_item (bullet_conj) (nat_number))
        (conj_item (bullet_conj) (nat_number))
      )
      (identifier) (all_map_to) (disj_list
        (disj_item (bullet_disj) (nat_number))
        (disj_item (bullet_disj) (nat_number))
      )
    )
  )
(double_line)))

==============================|||
Set of Records
==============================|||

---- MODULE Test ----
op == [
  foo : Nat,
  bar : Int,
  baz : Real
]
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (set_of_records
      (identifier) (nat_number_set)
      (identifier) (int_number_set)
      (identifier) (real_number_set)
    )
  )
(double_line)))

==============================|||
Set of Records with JList
==============================|||

---- MODULE Test ----
op == [
  foo :
    /\ 1
    /\ 2,
      bar :
        \/ 3
        \/ 4
]
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (set_of_records
      (identifier) (conj_list
        (conj_item (bullet_conj) (nat_number))
        (conj_item (bullet_conj) (nat_number))
      )
      (identifier) (disj_list
        (disj_item (bullet_disj) (nat_number))
        (disj_item (bullet_disj) (nat_number))
      )
    )
  )
(double_line)))

==============================|||
Record Value
==============================|||

---- MODULE Test ----
op == foo.bar
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (record_value (identifier_ref) (identifier_ref))
  )
(double_line)))

==============================|||
Record Value Inside Jlist
==============================|||

---- MODULE Test ----
op ==
  /\ 1
  /\ foo.bar 

====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (record_value (identifier_ref) (identifier_ref)))
    )
  )
(double_line)))

