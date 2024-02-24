==================|||
PlusCal P-Syntax Processes
==================|||
---- MODULE Test ----
(* --algorithm Test
  process A = 1
    begin
    skip
  end process;
  
  fair+ process B \in Procs
    variables a;
    begin
    print a
  end process;
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
        (pcal_process
          (identifier)
          (nat_number)
          (pcal_algorithm_body
            (pcal_skip)))
        (pcal_process
          (identifier)
          (set_in)
          (identifier_ref)
          (pcal_var_decls
            (pcal_var_decl
              (identifier)))
          (pcal_algorithm_body
            (pcal_print
              (identifier_ref))))))
    (double_line)))

==================|||
PlusCal C-Syntax Processes
==================|||
---- MODULE Test ----
(* --algorithm Test {
  process (A = 1) {
    skip
  };
  
  fair+ process (B \in Procs )
    variables a; {
    print a
  };
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
        (pcal_process
          (identifier)
          (nat_number)
          (pcal_algorithm_body
            (pcal_skip)))
        (pcal_process
          (identifier)
          (set_in)
          (identifier_ref)
          (pcal_var_decls
            (pcal_var_decl
              (identifier)))
          (pcal_algorithm_body
            (pcal_print
              (identifier_ref))))))
    (double_line)))
