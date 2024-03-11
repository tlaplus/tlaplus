=============|||
Basic CASE
=============|||

---- MODULE Test ----
op ==
    CASE 1 -> 2
    [] 3 -> 4
    [] OTHER -> 5
====

--------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (case
      (case_arm (nat_number) (case_arrow) (nat_number))
      (case_box) (case_arm (nat_number) (case_arrow) (nat_number))
      (case_box) (other_arm (case_arrow) (nat_number))
    )
  )
(double_line)))

=============|||
Solitary CASE
=============|||

---- MODULE Test ----
op == CASE 1 -> 2
====

--------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (case (case_arm (nat_number) (case_arrow) (nat_number)))
  )
(double_line)))

=============|||
CASE with dangling else
=============|||

---- MODULE Test ----
op ==
  CASE 1 ->
  CASE 2 -> 3
  [] OTHER -> 4
====

--------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (case (case_arm (nat_number) (case_arrow)
      (case
        (case_arm (nat_number) (case_arrow) (nat_number))
        (case_box) (other_arm (case_arrow) (nat_number))
      )
    ))
  )
(double_line)))

=============|||
Conjlist with CASE
=============|||

---- MODULE Test ----
op ==
  /\  CASE 1 -> 2
      [] 3 -> 2
      [] OTHER -> 5
  /\ 6
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item
        (bullet_conj)
        (case
          (case_arm (nat_number) (case_arrow) (nat_number))
          (case_box) (case_arm (nat_number) (case_arrow) (nat_number))
          (case_box) (other_arm (case_arrow) (nat_number))
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Conjlist inside CASE
=============|||

---- MODULE Test ----
op ==
  CASE
    /\ 1
    /\ 2
      ->
        /\ 3
        /\ 4
  []
    /\ 5
    /\ 6
      ->
        /\ 7
        /\ 8
  [] OTHER ->
    /\ 7
    /\ 8
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (case
      (case_arm
        (conj_list (conj_item (bullet_conj) (nat_number)) (conj_item (bullet_conj) (nat_number)))
        (case_arrow)
        (conj_list (conj_item (bullet_conj) (nat_number)) (conj_item (bullet_conj) (nat_number)))
      )
      (case_box)
      (case_arm
        (conj_list (conj_item (bullet_conj) (nat_number)) (conj_item (bullet_conj) (nat_number)))
        (case_arrow)
        (conj_list (conj_item (bullet_conj) (nat_number)) (conj_item (bullet_conj) (nat_number)))
      )
      (case_box)
      (other_arm (case_arrow)
        (conj_list (conj_item (bullet_conj) (nat_number)) (conj_item (bullet_conj) (nat_number)))
      )
    )
  )
(double_line)))

=============|||
Disjlist with CASE
=============|||

---- MODULE Test ----
op ==
  \/  CASE 1 -> 2
      [] 3 -> 2
      [] OTHER -> 5
  \/ 6
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item
        (bullet_disj)
        (case
          (case_arm (nat_number) (case_arrow) (nat_number))
          (case_box) (case_arm (nat_number) (case_arrow) (nat_number))
          (case_box) (other_arm (case_arrow) (nat_number))
        )
      )
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Disjlist inside CASE
=============|||

---- MODULE Test ----
op ==
  CASE
    \/ 1
    \/ 2
      ->
        \/ 3
        \/ 4
  []
    \/ 5
    \/ 6
      ->
        \/ 7
        \/ 8
  [] OTHER ->
    \/ 7
    \/ 8
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (case
      (case_arm
        (disj_list (disj_item (bullet_disj) (nat_number)) (disj_item (bullet_disj) (nat_number)))
        (case_arrow)
        (disj_list (disj_item (bullet_disj) (nat_number)) (disj_item (bullet_disj) (nat_number)))
      )
      (case_box)
      (case_arm
        (disj_list (disj_item (bullet_disj) (nat_number)) (disj_item (bullet_disj) (nat_number)))
        (case_arrow)
        (disj_list (disj_item (bullet_disj) (nat_number)) (disj_item (bullet_disj) (nat_number)))
      )
      (case_box)
      (other_arm (case_arrow)
        (disj_list (disj_item (bullet_disj) (nat_number)) (disj_item (bullet_disj) (nat_number)))
      )
    )
  )
(double_line)))

