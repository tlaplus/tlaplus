==================|||
PlusCal P-Syntax Either
==================|||
---- MODULE Test ----
(* --algorithm Test
begin
  either print "a"
  or print "b"
  or print "c"
end either ;
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
          (pcal_either
            (pcal_print
              (string))
            (pcal_print
              (string))
            (pcal_print
              (string))
            (pcal_end_either)))))
    (double_line)))

==================|||
PlusCal C-Syntax Either
==================|||
---- MODULE Test ----
(* --algorithm Test {
  {
    either { print "a" }
    or { print "b" }
    or { print "c" };
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
          (pcal_either
            (pcal_algorithm_body
              (pcal_print
                (string)))
            (pcal_algorithm_body
              (pcal_print
                (string)))
            (pcal_algorithm_body
              (pcal_print
                (string)))))))
    (double_line)))
