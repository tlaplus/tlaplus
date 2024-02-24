==================|||
PlusCal Goto
==================|||
---- MODULE Test ----
(* --algorithm Test
begin
  goto A; goto B
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
          (pcal_goto
            (identifier))
          (pcal_goto
            (identifier)))))
    (double_line)))
