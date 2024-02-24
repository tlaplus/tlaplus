==================|||
PlusCal P-Syntax Definitions
==================|||
---- MODULE Test ----
(* --algorithm Test
variables x = {}
define
  Op(p) == p
end define;
begin
  Op(1)
end algorithm; *)
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
        (pcal_var_decls
          (pcal_var_decl
            (identifier)
            (finite_set_literal)))
        (pcal_definitions
          (operator_definition
            (identifier)
            (identifier)
            (def_eq)
            (identifier_ref)))
        (pcal_algorithm_body
          (pcal_macro_call
            (identifier)
            (nat_number))))
      (block_comment_text))
    (double_line)))

==================|||
PlusCal C-Syntax Definitions
==================|||
---- MODULE Test ----
(* --algorithm Test {
  variables x = {}
  define { Op(p) == p }
  { Op(1) }
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
        (pcal_var_decls
          (pcal_var_decl
            (identifier)
            (finite_set_literal)))
        (pcal_definitions
          (operator_definition
            (identifier)
            (identifier)
            (def_eq)
            (identifier_ref)))
        (pcal_algorithm_body
          (pcal_macro_call
            (identifier)
            (nat_number)))))
    (double_line)))
