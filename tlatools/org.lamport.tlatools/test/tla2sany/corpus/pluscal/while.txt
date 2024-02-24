==================|||
PlusCal P-Syntax While
==================|||
---- MODULE Test ----
(* --algorithm Test
begin
  while x do skip end while;
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
          (pcal_while
            (identifier_ref)
            (pcal_skip)
            (pcal_end_while)))))
    (double_line)))

==================|||
PlusCal C-Syntax While
==================|||
---- MODULE Test ----
(* --algorithm Test {
  {
    while (x) { skip };
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
          (pcal_while
            (identifier_ref)
            (pcal_algorithm_body
              (pcal_skip))))))
    (double_line)))
