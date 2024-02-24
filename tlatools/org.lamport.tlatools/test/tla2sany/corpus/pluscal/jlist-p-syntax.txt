==================|||
PlusCal Block After Conjlist
==================|||
---- MODULE Test ----
op ==
  /\ 1
  /\ 2

(* --algorithm Test
begin
  assert TRUE
end algorithm *)
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
begin
  assert TRUE
end algorithm *)
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
begin assert
  /\ 3
  /\ 4 
end algorithm *)
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
begin assert
  /\ 3
  /\ 4 
end algorithm *)
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
begin assert
  /\ 3
(* --algorithm Nest1
begin assert
  /\ 4
(* --algorithm Nest0
begin assert
  /\ 5
  /\ 6
end algorithm *)
  /\ 7
end algorithm *)
  /\ 8 
end algorithm *)
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
begin assert
  /\ 3
  /\ 4 
end algorithm
--algorithm Test
begin assert
  /\ 5
  /\ 6 
end algorithm *)
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