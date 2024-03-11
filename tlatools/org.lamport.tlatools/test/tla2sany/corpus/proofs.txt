===============================|||
Theorem Without Proof
===============================|||

---- MODULE Test ----
THEOREM TRUE
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean))
(double_line)))

===============================|||
Named Theorem Without Proof
===============================|||

---- MODULE Test ----
PROPOSITION x == TRUE
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (identifier) (def_eq) (boolean))
(double_line)))

===============================|||
Obvious Proof
===============================|||

---- MODULE Test ----
LEMMA TRUE
OBVIOUS
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean) (terminal_proof))
(double_line)))

===============================|||
Named Obvious Proof
===============================|||

---- MODULE Test ----
COROLLARY def == TRUE
PROOF OBVIOUS
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (identifier) (def_eq) (boolean) (terminal_proof))
(double_line)))

===============================|||
Omitted Proof
===============================|||

---- MODULE Test ----
THEOREM x == TRUE
PROOF OMITTED
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (identifier) (def_eq) (boolean) (terminal_proof))
(double_line)))

===============================|||
Proof by Definition
===============================|||

---- MODULE Test ----
PROPOSITION TRUE
PROOF BY DEF >
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean)
    (terminal_proof (use_body
      (use_body_def (infix_op_symbol (gt)))
    ))
  )
(double_line)))

===============================|||
Proof by Multiple Definitions
===============================|||

---- MODULE Test ----
LEMMA TRUE
PROOF BY ONLY
  P,
  MODULE Naturals,
  Q,
  MODULE Integers
  DEFS
    >,
    R,
    MODULE Reals,
    =
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean)
    (terminal_proof (use_body
      (use_body_expr
        (identifier_ref)
        (module_ref (identifier_ref))
        (identifier_ref)
        (module_ref (identifier_ref))
      )
      (use_body_def
        (infix_op_symbol (gt))
        (identifier_ref)
        (module_ref (identifier_ref))
        (infix_op_symbol (eq))
      )
    ))
  )
(double_line)))

===============================|||
Proof by QED
===============================|||

---- MODULE Test ----
COROLLARY TRUE
PROOF <1>a QED BY <1>a, <*>a
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean)
    (non_terminal_proof
      (qed_step (proof_step_id (level) (name))
        (terminal_proof (use_body (use_body_expr
          (proof_step_ref (level) (name))
          (proof_step_ref (level) (name))
        )))
      )
    )
  )
(double_line)))

===============================|||
Proof with Variety of Step Types
===============================|||

---- MODULE Test ----
THEOREM TRUE
<1>a..... op == 1
<1>b..... DEFINE op2 == 2
<1>c..... HAVE 3
<1>d..... WITNESS 2, 3
<1>e..... TAKE a, b, c
<1>f..... <1>a
<1>g..... SUFFICES 5
<1>h..... CASE 6
<1>i..... PICK a, b, c : 7
<1>j..... HIDE 8
<1>k..... USE 9
<1>l..... INSTANCE M
<1>m..... QED
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean)
    (non_terminal_proof
      (proof_step (proof_step_id (level) (name)) (definition_proof_step (operator_definition (identifier) (def_eq) (nat_number))))
      (proof_step (proof_step_id (level) (name)) (definition_proof_step (operator_definition (identifier) (def_eq) (nat_number))))
      (proof_step (proof_step_id (level) (name)) (have_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (witness_proof_step (nat_number) (nat_number)))
      (proof_step (proof_step_id (level) (name)) (take_proof_step (identifier) (identifier) (identifier)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (proof_step_ref (level) (name))))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (case_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (pick_proof_step (identifier) (identifier) (identifier) (nat_number)))
      (proof_step (proof_step_id (level) (name)) (use_or_hide (use_body (use_body_expr (nat_number)))))
      (proof_step (proof_step_id (level) (name)) (use_or_hide (use_body (use_body_expr (nat_number)))))
      (proof_step (proof_step_id (level) (name)) (instance (identifier_ref)))
      (qed_step (proof_step_id (level) (name)))
    )
  )
(double_line)))

===============================|||
Stepped Proof by Definition
===============================|||

---- MODULE Test ----
PROPOSITION P => Q
PROOF
  <1> P
  <1> Q
    PROOF BY P
  <1> QED
=====================

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (bound_infix_op (identifier_ref) (implies) (identifier_ref))
    (non_terminal_proof
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (identifier_ref)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (identifier_ref)
        (terminal_proof (use_body (use_body_expr (identifier_ref))))
      ))
      (qed_step (proof_step_id (level) (name)))
    )
  )
(double_line)))

===============================|||
Proof with Star Steps
===============================|||

---- MODULE Test ----
LEMMA TRUE
<*> 1
<0> 2
<*> 3
<0> 4
<*> 5
<0> QED
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean)
    (non_terminal_proof
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (qed_step (proof_step_id (level) (name)))
    )
  )
(double_line)))

===============================|||
Proof with Plus Step
===============================|||

---- MODULE Test ----
COROLLARY TRUE
<+> 1
<0> 2
<*> 3
<0> 4
<*> 5
<0> QED
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean)
    (non_terminal_proof
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (qed_step (proof_step_id (level) (name)))
    )
  )
(double_line)))

===============================|||
Nested Proof
===============================|||

---- MODULE Test ----
THEOREM TRUE
PROOF
<*> 1
<0> 2
  <+> 3
  <1> 4
  <*> QED
<0> 5
<*> 6
<0> QED
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean)
    (non_terminal_proof
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number) (non_terminal_proof
        (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
        (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
        (qed_step (proof_step_id (level) (name)))
      )))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (qed_step (proof_step_id (level) (name)))
    )
  )
(double_line)))

===============================|||
Nested Proof Off QED
===============================|||

---- MODULE Test ----
PROPOSITION TRUE
PROOF
<*> 1
  PROOF
  <+> 2
  <1> QED
    PROOF
    <*> 3
      <1000> 4
      <*> QED
    <2> QED
<0> QED
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean)
    (non_terminal_proof
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number) (non_terminal_proof
        (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
        (qed_step (proof_step_id (level) (name)) (non_terminal_proof
          (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number) (non_terminal_proof
            (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
            (qed_step (proof_step_id (level) (name)))
          )))
          (qed_step (proof_step_id (level) (name)))
        ))
      )))
      (qed_step (proof_step_id (level) (name)))
    )
  )
(double_line)))


===============================|||
Proof with Nested Terminal Proof
===============================|||

---- MODULE Test ----
LEMMA TRUE
PROOF
<*> 1
  <+> 2
  <1> QED
    PROOF BY P
<*> 3
  <+> 4
  <1> QED
    OBVIOUS
<*> 5
  <+> 6
  <1> QED
    PROOF OMITTED
<*> 7
<0> QED
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean)
    (non_terminal_proof
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number) (non_terminal_proof
        (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
        (qed_step (proof_step_id (level) (name)) (terminal_proof (use_body (use_body_expr (identifier_ref)))))
      )))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number) (non_terminal_proof
        (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
        (qed_step (proof_step_id (level) (name)) (terminal_proof))
      )))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number) (non_terminal_proof
        (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
        (qed_step (proof_step_id (level) (name)) (terminal_proof))
      )))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (qed_step (proof_step_id (level) (name)))
    )
  )
(double_line)))

===============================|||
Implicit Nested Proof Levels
===============================|||

---- MODULE Test ----
COROLLARY TRUE
<*> 1
  <+> 2
    <+> 3
      <+> 4
      <*> QED
    <*> QED
  <*> 5
    <+> 6
    <*> QED
  <*> QED
<*> 7
<*> QED
====

-------------------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean)
    (non_terminal_proof
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number) (non_terminal_proof
        (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number) (non_terminal_proof
          (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number) (non_terminal_proof
            (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
            (qed_step (proof_step_id (level) (name)))
          )))
          (qed_step (proof_step_id (level) (name)))
        )))
        (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number) (non_terminal_proof
          (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
          (qed_step (proof_step_id (level) (name)))
        )))
        (qed_step (proof_step_id (level) (name)))
      )))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (qed_step (proof_step_id (level) (name)))
    )
  )
(double_line)))

==============================|||
Proof Containing Jlist
==============================|||

---- MODULE Test ----
THEOREM TRUE
<*>a1a...
  /\ 1
  /\ \/ 2
   <+>b2b... WITNESS
     \/ 3
     \/ /\ 4,
     /\ \/ 5
     /\ 6
   <*>c3c... QED BY
     /\ 7
     /\ \/ 8,
     \/ /\ 9
     \/ 10
<*>d4d... QED BY
  \/ 11
  \/ /\ 12,
  /\ \/ 13
  /\ 14
====

------------------------------|||


(source_file (module (header_line) (identifier) (header_line)
  (theorem (boolean) (non_terminal_proof
    (proof_step (proof_step_id (level) (name)) (suffices_proof_step
      (conj_list
        (conj_item (bullet_conj) (nat_number))
        (conj_item (bullet_conj) (disj_list (disj_item (bullet_disj) (nat_number))))
      )
      (non_terminal_proof
        (proof_step (proof_step_id (level) (name)) (witness_proof_step
          (disj_list
            (disj_item (bullet_disj) (nat_number))
            (disj_item (bullet_disj) (conj_list (conj_item (bullet_conj) (nat_number))))
          )
          (conj_list
            (conj_item (bullet_conj) (disj_list (disj_item (bullet_disj) (nat_number))))
            (conj_item (bullet_conj) (nat_number))
          )
        ))
        (qed_step (proof_step_id (level) (name)) (terminal_proof (use_body (use_body_expr
          (conj_list
            (conj_item (bullet_conj) (nat_number))
            (conj_item (bullet_conj) (disj_list (disj_item (bullet_disj) (nat_number))))
          )
          (disj_list
            (disj_item (bullet_disj) (conj_list (conj_item (bullet_conj) (nat_number))))
            (disj_item (bullet_disj) (nat_number))
          )
        ))))
      )
    ))
    (qed_step (proof_step_id (level) (name)) (terminal_proof (use_body (use_body_expr
      (disj_list
        (disj_item (bullet_disj) (nat_number))
        (disj_item (bullet_disj) (conj_list (conj_item (bullet_conj) (nat_number))))
      )
      (conj_list
        (conj_item (bullet_conj) (disj_list (disj_item (bullet_disj) (nat_number))))
        (conj_item (bullet_conj) (nat_number))
      )
    ))))
  ))
(double_line)))

