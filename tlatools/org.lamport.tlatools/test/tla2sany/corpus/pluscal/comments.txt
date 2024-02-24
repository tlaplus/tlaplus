==================|||
PlusCal Comments
==================|||
---- MODULE Test ----
(* 
zero
--algorithm Test
(* one 
  (* two (* three \* four *)*)
*)

\* five
begin
  skip \* six (* seven *)
end algorithm *)
====
-------------|||

(source_file
  (module
    (header_line)
    (identifier)
    (header_line)
    (block_comment
      (block_comment_text)
      (pcal_algorithm
        (pcal_algorithm_start)
        (identifier)
        (block_comment
          (block_comment_text)
          (block_comment
            (block_comment_text)
            (block_comment
              (block_comment_text))))
        (comment)
        (pcal_algorithm_body
          (pcal_skip))
        (comment)))
    (double_line)))

==================|||
PlusCal Fair Algorithm
==================|||
---- MODULE Test ----
(*
--fair algorithm Test
begin
  skip;
end algorithm
*)
====
-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (block_comment
    (pcal_algorithm (pcal_algorithm_start (fair)) (identifier)
      (pcal_algorithm_body
        (pcal_skip)
      )
    )
  )
(double_line)))

