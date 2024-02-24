=============|||
Basic Conjlist
=============|||

---- MODULE Test ----
op ==
    /\ 1
    /\ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Inline Conjlist
=============|||

---- MODULE Test ----
op == /\ 1
      /\ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Start-of-Line Conjlist
=============|||

---- MODULE Test ----
op ==
/\ 1
/\ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Left-Shifted Conjlist
=============|||

---- MODULE Test ----
op ==
 /\ 1
/\ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (conj_list (conj_item (bullet_conj) (nat_number)))
      (land)
      (nat_number)
    )
  )
(double_line)))

=============|||
Right-Shifted Conjlist
=============|||

---- MODULE Test ----
op ==
/\ 1
 /\ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item
        (bullet_conj)
        (bound_infix_op
          (nat_number)
          (land)
          (nat_number)
        )
      )
    )
  )
(double_line)))

=============|||
Separated Conjlist
=============|||

---- MODULE Test ----
op ==
  /\ 1

  /\ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Multiline Conjlist
=============|||

---- MODULE Test ----
op ==
  /\ 
   1
  /\
   2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Nested Conjlist
=============|||

---- MODULE Test ----
op ==
 /\ /\ 1
    /\ 2
 /\ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item
        (bullet_conj)
        (conj_list
          (conj_item (bullet_conj) (nat_number))
          (conj_item (bullet_conj) (nat_number))
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Start-of-Line Nested Conjlist
=============|||

---- MODULE Test ----
op ==
/\ /\ 1
   /\ 2
/\ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj)
        (conj_list
          (conj_item (bullet_conj) (nat_number))
          (conj_item (bullet_conj) (nat_number))
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Infix Op Conjlist
=============|||

---- MODULE Test ----
op ==
 /\ 1
  + 2 
 /\ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item
        (bullet_conj)
        (bound_infix_op
          (nat_number)
          (plus)
          (nat_number)
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Division Infix Op Conjlist
=============|||

---- MODULE Test ----
op ==
 /\ 1
  / 2 
 /\ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item
        (bullet_conj)
        (bound_infix_op
          (nat_number)
          (slash)
          (nat_number)
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Infix Op Terminated Conjlist
=============|||

---- MODULE Test ----
op ==
 /\ 1
 + 2 
 /\ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (bound_infix_op
        (conj_list (conj_item (bullet_conj) (nat_number)))
        (plus)
        (nat_number)
      )
      (land)
      (nat_number)
    )
  )
(double_line)))

=============|||
Division Infix Op Terminated Conjlist
=============|||

---- MODULE Test ----
op ==
 /\ 1
 / 2 
 /\ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (bound_infix_op
        (conj_list (conj_item (bullet_conj) (nat_number)))
        (slash)
        (nat_number)
      )
      (land)
      (nat_number)
    )
  )
(double_line)))

=============|||
Not a Conjlist
=============|||

---- MODULE Test ----
op == 1 /\ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (nat_number)
      (land)
      (nat_number)
    )
  )
(double_line)))

=============|||
Conjlist with Parentheses
=============|||

---- MODULE Test ----
op ==
  /\ (1)
  /\ (2)
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (parentheses (nat_number)))
      (conj_item (bullet_conj) (parentheses (nat_number)))
    )
  )
(double_line)))

=============|||
Conjlist Terminated by Parentheses
=============|||

---- MODULE Test ----
op == (
  /\ 1
   )
  /\ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (parentheses
        (conj_list (conj_item (bullet_conj) (nat_number)))
      )
      (land)
      (nat_number)
    )
  )
(double_line)))

=============|||
Nested Conjlist Terminated by Parentheses
=============|||

---- MODULE Test ----
op == (
  /\ 1
  /\  /\ 2
      /\ 3
       )
  /\ 4
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (parentheses
        (conj_list
          (conj_item (bullet_conj) (nat_number))
          (conj_item
            (bullet_conj)
            (conj_list
              (conj_item (bullet_conj) (nat_number))
              (conj_item (bullet_conj) (nat_number))
            )
          )
        )
      )
      (land)
      (nat_number)
    )
  )
(double_line)))

=============|||
Double-Nested Conjlist Terminated by Parentheses
=============|||

---- MODULE Test ----
op ==
  /\ 1
  /\  /\ 2 + (
        /\ 3
        /\ 4
          )
      /\ 5
  /\ 6
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item
        (bullet_conj)
        (conj_list
          (conj_item
            (bullet_conj)
            (bound_infix_op
              (nat_number)
              (plus)
              (parentheses
                (conj_list
                  (conj_item (bullet_conj) (nat_number))
                  (conj_item (bullet_conj) (nat_number))
                )
              )
            )
          )
          (conj_item (bullet_conj) (nat_number))
        )
      )
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Module-End-Terminated Conjlist
=============|||

---- MODULE Test ----
op ==
  /\ 1
  /\ 2  ====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

=============|||
Keyword-Unit-Terminated Conjlist
=============|||

---- MODULE Test ----
op1 ==
  /\ 1
  /\ 2
      ASSUME x

op2 ==
  /\ 3
  /\ 4
      LOCAL INSTANCE ModuleName

op3 ==
  /\ 5
  /\ 6
      -----------------

op4 ==
  /\ 7
  /\ 8
      ---- MODULE Nested ----
      ====

op5 ==
  /\ 9
  /\ 10
      VARIABLES x, y
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
    )
  )
  (assumption (identifier_ref))
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
    )
  )
  (local_definition (instance (identifier_ref)))
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
    )
  )
  (single_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
    )
  )
  (module (header_line) (identifier) (header_line) (double_line))
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
    )
  )
  (variable_declaration (identifier) (identifier))
(double_line)))

=============|||
Conjlist with Empty Tuple
=============|||

---- MODULE Test ----
op ==
  /\ 1
  /\ <<>>
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (tuple_literal (langle_bracket) (rangle_bracket)))
    )
  )
(double_line)))

=============|||
Conjlist with Empty Set
=============|||

---- MODULE Test ----
op ==
  /\ 1
  /\ {}
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (finite_set_literal))
    )
  )
(double_line)))
