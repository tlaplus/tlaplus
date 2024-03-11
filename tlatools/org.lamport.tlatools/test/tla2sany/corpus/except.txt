=============|||
Basic record update
=============|||

---- MODULE Test ----
r == [a EXCEPT ![2] = "a"]
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: 
        (except 
            expr_to_update: (identifier_ref) 
            (except_update
              update_specifier: 
                (except_update_specifier
                    (except_update_fn_appl (nat_number)))
              new_val: (string))
        ))
(double_line)))

=============|||
Single nested record update
=============|||

---- MODULE Test ----
r == [a EXCEPT ![2]["a"][3] = @ + 1]
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (except 
      expr_to_update: (identifier_ref) 
      (except_update
        update_specifier: (except_update_specifier
          (except_update_fn_appl (nat_number))
          (except_update_fn_appl (string))
          (except_update_fn_appl (nat_number))
        )
        new_val: (bound_infix_op lhs: (prev_func_val) symbol: (plus) rhs: (nat_number))
      )
    )
  )
(double_line)))

=============|||
Single nested record update with dot syntax
=============|||

---- MODULE Test ----
r == [a EXCEPT !.x.y.z = "b"]
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: 
        (except 
            expr_to_update: (identifier_ref) 
            (except_update
              update_specifier: 
                (except_update_specifier
                    (except_update_record_field (identifier_ref))
                    (except_update_record_field (identifier_ref))
                    (except_update_record_field (identifier_ref)))
              new_val: (string))
        ))
(double_line)))

=============|||
Multiple nested record updates
=============|||

---- MODULE Test ----
r == [a EXCEPT ![2]["a"][3] = @, !["b"][x] = 5, ![y][z] = "c"]
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: 
        (except 
            expr_to_update: (identifier_ref) 
            (except_update
              update_specifier: 
                (except_update_specifier
                    (except_update_fn_appl (nat_number))
                    (except_update_fn_appl (string))
                    (except_update_fn_appl (nat_number)))
              new_val: (prev_func_val))
            (except_update
              update_specifier: 
                (except_update_specifier
                    (except_update_fn_appl (string))
                    (except_update_fn_appl (identifier_ref)))
              new_val: (nat_number))
            (except_update
              update_specifier: 
                (except_update_specifier
                    (except_update_fn_appl (identifier_ref))
                    (except_update_fn_appl (identifier_ref)))
              new_val: (string))
        ))
(double_line)))

=============|||
Multiple nested record updates with dot syntax
=============|||

---- MODULE Test ----
r == [a EXCEPT !.a.b.c = @, !.b.x = 5]
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: 
        (except 
            expr_to_update: (identifier_ref) 
            (except_update
              update_specifier: 
                (except_update_specifier
                    (except_update_record_field (identifier_ref))
                    (except_update_record_field (identifier_ref))
                    (except_update_record_field (identifier_ref)))
              new_val: (prev_func_val))
            (except_update
              update_specifier: 
                (except_update_specifier
                    (except_update_record_field (identifier_ref))
                    (except_update_record_field (identifier_ref)))
              new_val: (nat_number))
        ))
(double_line)))

=============|||
Multiple nested record updates with mixed dot/function syntax
=============|||

---- MODULE Test ----
r == [a EXCEPT !.a.b["c"] = "b", ![2].x = @]
====

-------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: 
        (except 
            expr_to_update: (identifier_ref) 
            (except_update
              update_specifier: 
                (except_update_specifier
                    (except_update_record_field (identifier_ref))
                    (except_update_record_field (identifier_ref))
                    (except_update_fn_appl (string)))
              new_val: (string))
            (except_update
              update_specifier: 
                (except_update_specifier
                    (except_update_fn_appl (nat_number))
                    (except_update_record_field (identifier_ref)))
              new_val: (prev_func_val))
        ))
(double_line)))

