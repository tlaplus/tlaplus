==================|||
PlusCal P-Syntax With
==================|||
---- MODULE Test ----
(* --algorithm Test
begin
  with x=1; y \in {} do skip end with ;
end algorithm *)
====
-------------|||

(source_file
  (module
    (header_line)
    (identifier)
    (header_line)
    (block_comment
      (pcal_algorithm
        (pcal_algorithm_start)
        (identifier)
        (pcal_algorithm_body
          (pcal_with
            (identifier)
            (nat_number)
            (identifier)
            (set_in)
            (finite_set_literal)
            (pcal_skip)
            (pcal_end_with)))))
    (double_line)))

==================|||
PlusCal C-Syntax With
==================|||
---- MODULE Test ----
(* --algorithm Test {
  {
    with (x=1; y \in {}) { skip; };
  }
} *)
====
-------------|||

(source_file
  (module
    (header_line)
    (identifier)
    (header_line)
    (block_comment
      (pcal_algorithm
        (pcal_algorithm_start)
        (identifier)
        (pcal_algorithm_body
          (pcal_with
            (identifier)
            (nat_number)
            (identifier)
            (set_in)
            (finite_set_literal)
            (pcal_algorithm_body
              (pcal_skip))))))
    (double_line)))
