==================|||
PlusCal P-Syntax Macros
==================|||
---- MODULE Test ----
(* --algorithm Test
macro M(var1, var2)
begin
  skip;
end macro;
begin
 P(1, "1")
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
        (pcal_macro
          (pcal_macro_decl
            (identifier)
            (identifier)
            (identifier))
          (pcal_algorithm_body
            (pcal_skip)))
        (pcal_algorithm_body
          (pcal_macro_call
            (identifier)
            (nat_number)
            (string)))))
    (double_line)))

==================|||
PlusCal C-Syntax Macros
==================|||
---- MODULE Test ----
(* --algorithm Test {
macro M(var1, var2) { skip; }
{
  P(1, "1")
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
        (pcal_macro
          (pcal_macro_decl
            (identifier)
            (identifier)
            (identifier))
          (pcal_algorithm_body
            (pcal_skip)))
        (pcal_algorithm_body
          (pcal_macro_call
            (identifier)
            (nat_number)
            (string)))))
    (double_line)))
