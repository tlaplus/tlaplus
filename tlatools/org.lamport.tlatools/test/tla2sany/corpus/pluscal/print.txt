==================|||
PlusCal Print
==================|||
---- MODULE Test ----
(* --algorithm Test
begin
  print {1, "a", [x |-> 0]}
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
          (pcal_print
            (finite_set_literal
              (nat_number)
              (string)
              (record_literal
                (identifier)
                (all_map_to)
                (nat_number)))))))
    (double_line)))
