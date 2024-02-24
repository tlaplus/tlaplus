==================|||
PlusCal Await (When)
==================|||
---- MODULE Test ----
(* --algorithm Test
begin
  await test;
  when ¬ test;
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
          (pcal_await
            (identifier_ref))
          (pcal_await
            (bound_prefix_op
              (lnot)
              (identifier_ref))))))
    (double_line)))
