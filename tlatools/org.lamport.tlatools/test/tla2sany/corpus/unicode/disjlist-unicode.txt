=============|||
Basic Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
    ∨ 1
    ∨ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Inline Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜ ∨ 1
     ∨ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Start-of-Line Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
∨ 1
∨ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Left-Shifted Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
 ∨ 1
∨ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (disj_list (disj_item (bullet_disj) (nat_number)))
      (lor)
      (nat_number)
    )
  )
(double_line)))

=============|||
Right-Shifted Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
∨ 1
 ∨ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item
        (bullet_disj)
        (bound_infix_op
          (nat_number)
          (lor)
          (nat_number)
        )
      )
    )
  )
(double_line)))

=============|||
Separated Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
  ∨ 1

  ∨ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Multiline Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
  ∨
   1
  ∨
   2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Nested Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
 ∨ ∨ 1
   ∨ 2
 ∨ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item
        (bullet_disj)
        (disj_list
          (disj_item (bullet_disj) (nat_number))
          (disj_item (bullet_disj) (nat_number))
        )
      )
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Start-of-Line Nested Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
∨ ∨ 1
  ∨ 2
∨ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj)
        (disj_list
          (disj_item (bullet_disj) (nat_number))
          (disj_item (bullet_disj) (nat_number))
        )
      )
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Infix Op Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
 ∨ 1
  + 2
 ∨ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item
        (bullet_disj)
        (bound_infix_op
          (nat_number)
          (plus)
          (nat_number)
        )
      )
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Division Infix Op Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
 ∨ 1
  / 2
 ∨ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item
        (bullet_disj)
        (bound_infix_op
          (nat_number)
          (slash)
          (nat_number)
        )
      )
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Infix Op Terminated Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
 ∨ 1
 + 2
 ∨ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (bound_infix_op
        (disj_list (disj_item (bullet_disj) (nat_number)))
        (plus)
        (nat_number)
      )
      (lor)
      (nat_number)
    )
  )
(double_line)))

=============|||
Division Infix Op Terminated Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
 ∨ 1
 / 2
 ∨ 3
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (bound_infix_op
        (disj_list (disj_item (bullet_disj) (nat_number)))
        (slash)
        (nat_number)
      )
      (lor)
      (nat_number)
    )
  )
(double_line)))

=============|||
Not a Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜ 1 ∨ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (nat_number)
      (lor)
      (nat_number)
    )
  )
(double_line)))

=============|||
Unicode Disjlist with Parentheses
=============|||

---- MODULE Test ----
op ≜
  ∨ (1)
  ∨ (2)
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (parentheses (nat_number)))
      (disj_item (bullet_disj) (parentheses (nat_number)))
    )
  )
(double_line)))

=============|||
Unicode Disjlist Terminated by Parentheses
=============|||

---- MODULE Test ----
op ≜ (
  ∨ 1
   )
  ∨ 2
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (parentheses
        (disj_list (disj_item (bullet_disj) (nat_number)))
      )
      (lor)
      (nat_number)
    )
  )
(double_line)))

=============|||
Nested Unicode Disjlist Terminated by Parentheses
=============|||

---- MODULE Test ----
op ≜ (
  ∨ 1
  ∨  ∨ 2
     ∨ 3
       )
  ∨ 4
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (parentheses
        (disj_list
          (disj_item (bullet_disj) (nat_number))
          (disj_item
            (bullet_disj)
            (disj_list
              (disj_item (bullet_disj) (nat_number))
              (disj_item (bullet_disj) (nat_number))
            )
          )
        )
      )
      (lor)
      (nat_number)
    )
  )
(double_line)))

=============|||
Double-Nested Unicode Disjlist Terminated by Parentheses
=============|||

---- MODULE Test ----
op ≜
  ∨ 1
  ∨  ∨ 2 + (
        ∨ 3
        ∨ 4
          )
     ∨ 5
  ∨ 6
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item
        (bullet_disj)
        (disj_list
          (disj_item
            (bullet_disj)
            (bound_infix_op
              (nat_number)
              (plus)
              (parentheses
                (disj_list
                  (disj_item (bullet_disj) (nat_number))
                  (disj_item (bullet_disj) (nat_number))
                )
              )
            )
          )
          (disj_item (bullet_disj) (nat_number))
        )
      )
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Module-End-Terminated Unicode Disjlist
=============|||

---- MODULE Test ----
op ≜
  ∨ 1
  ∨ 2  ====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

=============|||
Keyword-Unit-Terminated Unicode Disjlist
=============|||

---- MODULE Test ----
op1 ≜
  ∨ 1
  ∨ 2
      ASSUME x

op2 ≜
  ∨ 3
  ∨ 4
      LOCAL INSTANCE ModuleName

op3 ≜
  ∨ 5
  ∨ 6
      -----------------

op4 ≜
  ∨ 7
  ∨ 8
      ---- MODULE Nested ----
      ====

op5 ≜
  ∨ 9
  ∨ 10
      VARIABLES x, y
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (nat_number))
    )
  )
  (assumption (identifier_ref))
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (nat_number))
    )
  )
  (local_definition (instance (identifier_ref)))
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (nat_number))
    )
  )
  (single_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (nat_number))
    )
  )
  (module (header_line) (identifier) (header_line) (double_line))
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (nat_number))
    )
  )
  (variable_declaration (identifier) (identifier))
(double_line)))

=============|||
Unicode Disjlist with Empty Tuple
=============|||

---- MODULE Test ----
op ≜
  ∨ 1
  ∨ ⟨⟩
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (tuple_literal (langle_bracket) (rangle_bracket)))
    )
  )
(double_line)))

=============|||
Unicode Disjlist with Empty Set
=============|||

---- MODULE Test ----
op ≜
  ∨ 1
  ∨ {}
====

-------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (disj_item (bullet_disj) (finite_set_literal))
    )
  )
(double_line)))
