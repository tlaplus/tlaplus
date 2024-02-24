==================|||
PlusCal Block After Conjlist
==================|||
---- MODULE Test ----
op ==
  /\ 1
  /\ 2

(* --algorithm Test
{{
  assert TRUE
}}*)
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
      (block_comment
        (pcal_algorithm (pcal_algorithm_start) (identifier)
          (pcal_algorithm_body (pcal_assert (boolean)))
        )
      )
    )
  )
(double_line)))

==================|||
PlusCal Block Inside Conjlist
==================|||
---- MODULE Test ----
op ==
  /\ 1
  /\ 2
(* --algorithm Test
{{
  assert TRUE
}} *)
  /\ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
      (block_comment
        (pcal_algorithm (pcal_algorithm_start) (identifier)
          (pcal_algorithm_body (pcal_assert (boolean)))
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

==================|||
PlusCal Block Containing Conjlist After Conjlist
==================|||
---- MODULE Test ----
op ==
  /\ 1
  /\ 2

(* --algorithm Test
{{ assert
  /\ 3
  /\ 4 
}} *)
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
      (block_comment
        (pcal_algorithm (pcal_algorithm_start) (identifier)
          (pcal_algorithm_body (pcal_assert
            (conj_list
              (conj_item (bullet_conj) (nat_number))
              (conj_item (bullet_conj) (nat_number))
            )
          ))
        )
      )
    )
  )
(double_line)))

==================|||
PlusCal Block Containing Conjlist Inside Conjlist
==================|||
---- MODULE Test ----
op ==
  /\ 1
  /\ 2
(* --algorithm Test
{{ assert
  /\ 3
  /\ 4 
}} *)
  /\ 5
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
      (block_comment
        (pcal_algorithm (pcal_algorithm_start) (identifier)
          (pcal_algorithm_body (pcal_assert
            (conj_list
              (conj_item (bullet_conj) (nat_number))
              (conj_item (bullet_conj) (nat_number))
            )
          ))
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

==================|||
Multiple Nested PlusCal Blocks
==================|||
---- MODULE Test ----
op ==
  /\ 1
  /\ 2
(* --algorithm Nest2
{{ assert
  /\ 3
(* --algorithm Nest1
{{ assert
  /\ 4
(* --algorithm Nest0
{{ assert
  /\ 5
  /\ 6
}} *)
  /\ 7
}} *)
  /\ 8 
}} *)
  /\ 9
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
      (block_comment
        (pcal_algorithm (pcal_algorithm_start) (identifier)
          (pcal_algorithm_body (pcal_assert
            (conj_list
              (conj_item (bullet_conj) (nat_number))
      (block_comment
        (pcal_algorithm (pcal_algorithm_start) (identifier)
          (pcal_algorithm_body (pcal_assert
            (conj_list
              (conj_item (bullet_conj) (nat_number))
      (block_comment
        (pcal_algorithm (pcal_algorithm_start) (identifier)
          (pcal_algorithm_body (pcal_assert
            (conj_list
              (conj_item (bullet_conj) (nat_number))
              (conj_item (bullet_conj) (nat_number))
            )
          ))
        )
      )
              (conj_item (bullet_conj) (nat_number))
            )
          ))
        )
      )
              (conj_item (bullet_conj) (nat_number))
            )
          ))
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

==================|||
Multiple PlusCal Blocks Inside Block Comment
==================|||
---- MODULE Test ----
op ==
  /\ 1
  /\ 2
(* --algorithm Test
{{ assert
  /\ 3
  /\ 4 
}}
--algorithm Test
{{ assert
  /\ 5
  /\ 6 
}} *)
  /\ 7
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
      (block_comment
        (pcal_algorithm (pcal_algorithm_start) (identifier)
          (pcal_algorithm_body (pcal_assert
            (conj_list
              (conj_item (bullet_conj) (nat_number))
              (conj_item (bullet_conj) (nat_number))
            )
          ))
        )
        (pcal_algorithm (pcal_algorithm_start) (identifier)
          (pcal_algorithm_body (pcal_assert
            (conj_list
              (conj_item (bullet_conj) (nat_number))
              (conj_item (bullet_conj) (nat_number))
            )
          ))
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))