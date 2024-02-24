==================|||
PlusCal Assert
==================|||
---- MODULE Test ----
(* --algorithm Test
begin
  assert TRUE
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
          (pcal_assert
            (boolean)))))
    (double_line)))
