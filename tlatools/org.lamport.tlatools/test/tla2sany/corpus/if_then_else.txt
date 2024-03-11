==================|||
ITE with Strings
==================|||

---- MODULE Test ----
op == IF "A" THEN "B" ELSE "C"
====

------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (if_then_else (string) (string) (string))
  )
(double_line)))

=============|||
Conjlist with ITE
=============|||

---- MODULE Test ----
op ==
  /\  IF 1
      THEN 2
      ELSE 3
  /\ 4
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item
        (bullet_conj)
        (if_then_else
          (nat_number)
          (nat_number)
          (nat_number)
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Conjlist inside ITE
=============|||

---- MODULE Test ----
op ==
  IF
    /\ 1
    /\ 2
      THEN 3
      ELSE 4
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (if_then_else
      (conj_list
        (conj_item (bullet_conj) (nat_number))
        (conj_item (bullet_conj) (nat_number))
      )
      (nat_number)
      (nat_number)
    )
  )
(double_line)))

=============|||
Disjlist with ITE
=============|||

---- MODULE Test ----
op ==
  \/  IF 1
      THEN 2
      ELSE 3
  \/ 4
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item
        (bullet_disj)
        (if_then_else
          (nat_number)
          (nat_number)
          (nat_number)
        )
      )
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Disjlist inside ITE
=============|||

---- MODULE Test ----
op ==
  IF
    \/ 1
    \/ 2
      THEN 3
      ELSE 4
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (if_then_else
      (disj_list
        (disj_item (bullet_disj) (nat_number))
        (disj_item (bullet_disj) (nat_number))
      )
      (nat_number)
      (nat_number)
    )
  )
(double_line)))
