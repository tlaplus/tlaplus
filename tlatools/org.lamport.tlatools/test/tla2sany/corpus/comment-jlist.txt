====================|||
Comment in Conjlist
====================|||

---- MODULE Test ----
op ==
  /\ 1
\* this should be ignored
  /\ 2
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (comment)
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

====================|||
Comment in Disjlist
====================|||

---- MODULE Test ----
op ==
  \/ 1
\* this should be ignored
  \/ 2
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (comment)
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

====================|||
Block Comment in Conjlist
====================|||

---- MODULE Test ----
op ==
  /\ 1
(* this should be ignored *)
  /\ 2
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (block_comment (block_comment_text))
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

====================|||
Block Comment in Disjlist
====================|||

---- MODULE Test ----
op ==
  \/ 1
(* this should be ignored *)
  \/ 2
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (block_comment (block_comment_text))
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

====================|||
Block Comment in Disjlist
====================|||

---- MODULE Test ----
op ==
  \/ 1
(* this should be ignored *)
  \/ 2
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (block_comment (block_comment_text))
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

====================|||
Block Comment Preceding Jlist Bullet
====================|||

---- MODULE Test ----
op ==
(*xxxxx*) /\ 1
(*xxxxx*) /\ 2
(*xxxxx*) /\ \/ 3
(*xxxxxxxx*) \/ 4
(*xxxxx*) /\ 5
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (block_comment (block_comment_text))
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (block_comment (block_comment_text))
      (conj_item (bullet_conj) (nat_number))
      (block_comment (block_comment_text))
      (conj_item (bullet_conj)
        (disj_list
          (disj_item (bullet_disj) (nat_number))
          (block_comment (block_comment_text))
          (disj_item (bullet_disj) (nat_number))
          (block_comment (block_comment_text))
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

====================|||
Block Comment Preceding Jlist Bullet From Previous Line
====================|||

---- MODULE Test ----
op == (*xxx
xxxxx*) /\ 1 (*xxx
xxxxx*) /\ 2 (*xxx
xxxxx*) /\ \/ 3 (*xxx
xxxxxxxx*) \/ 4 (*xxx
xxxxx*) /\ 5
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (block_comment (block_comment_text))
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (block_comment (block_comment_text))
      (conj_item (bullet_conj) (nat_number))
      (block_comment (block_comment_text))
      (conj_item (bullet_conj)
        (disj_list
          (disj_item (bullet_disj) (nat_number))
          (block_comment (block_comment_text))
          (disj_item (bullet_disj) (nat_number))
          (block_comment (block_comment_text))
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

