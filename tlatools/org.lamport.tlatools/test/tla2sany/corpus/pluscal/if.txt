==================|||
PlusCal P-Syntax If
==================|||
---- MODULE Test ----
(* --algorithm Test
begin
 if x then skip
 elsif x then skip;
 elsif x then skip
 else skip;
 end if
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
          (pcal_if
            (identifier_ref)
            (pcal_skip)
            (identifier_ref)
            (pcal_skip)
            (identifier_ref)
            (pcal_skip)
            (pcal_skip)
            (pcal_end_if)))))
    (double_line)))

==================|||
PlusCal C-Syntax If
==================|||
---- MODULE Test ----
(* --algorithm Test {
  {
    if (x) { skip }
    else { 
      if (x) { skip }
      else { skip }
    };
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
          (pcal_if
            (identifier_ref)
            (pcal_algorithm_body
              (pcal_skip))
            (pcal_algorithm_body
              (pcal_if
                (identifier_ref)
                (pcal_algorithm_body
                  (pcal_skip))
                (pcal_algorithm_body
                  (pcal_skip))))))))
    (double_line)))
