==================|||
PlusCal P-Syntax Procedures
==================|||
---- MODULE Test ----
(* --algorithm Test
procedure P(arg1, arg2)
variables var1 = "";
begin
  n0: skip;
  return;
end procedure;
begin
 call P(1, "1")
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
        (pcal_procedure
          (pcal_proc_decl
            (identifier)
            (pcal_proc_var_decl
              (identifier))
            (pcal_proc_var_decl
              (identifier))
            (pcal_proc_var_decls
              (pcal_proc_var_decl
                (identifier)
                (string))))
          (pcal_algorithm_body
            (identifier)
            (pcal_skip)
            (pcal_return)))
        (pcal_algorithm_body
          (pcal_proc_call
            (identifier)
            (nat_number)
            (string)))))
    (double_line)))

==================|||
PlusCal C-Syntax Procedures
==================|||
---- MODULE Test ----
(* --algorithm Test {
procedure P(arg1, arg2)
variables var1 = "";
{
  Label: skip;
  return;
}
{
 call P(1, "1")
}
}*)
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
        (pcal_procedure
          (pcal_proc_decl
            (identifier)
            (pcal_proc_var_decl
              (identifier))
            (pcal_proc_var_decl
              (identifier))
            (pcal_proc_var_decls
              (pcal_proc_var_decl
                (identifier)
                (string))))
          (pcal_algorithm_body
            (identifier)
            (pcal_skip)
            (pcal_return)))
        (pcal_algorithm_body
          (pcal_proc_call
            (identifier)
            (nat_number)
            (string)))))
    (double_line)))
