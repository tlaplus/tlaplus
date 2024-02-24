====================|||
Solitary Comment
====================|||

---- MODULE Test ----
\* This is a comment
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (comment)
(double_line)))

====================|||
Comment In Definition
====================|||

---- MODULE Test ----
op == \* This is a comment
    id
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (comment) (identifier_ref)
  )
(double_line)))

====================|||
Solitary Block Comment
====================|||

---- MODULE Test ----
(*
This
is
a
multi
line
comment
*)
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (block_comment (block_comment_text))
(double_line)))

====================|||
Block Comment in Expression
====================|||

---- MODULE Test ----
op == 1 +
(*
This
is
a
multi
line
comment
*)
2
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_infix_op
      (nat_number) (plus)
      (block_comment (block_comment_text))
      (nat_number)
    )
  )
(double_line)))

====================|||
Nested Block Comment
====================|||

---- MODULE Test ----
(*
This
is
a
(*nested*)
multi
line
comment
*)
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (block_comment 
    (block_comment_text 
      (block_comment
        (block_comment_text))))
(double_line)))

====================|||
Complicated Block Comment
====================|||

---- MODULE Test ----
(*
This
( * )
  is a
    (*(*complicated*) *and* (*nested*)*)
  (*multi
  line*)
comment
)
**()**
*)
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (block_comment
    (block_comment_text
      (block_comment
        (block_comment
          (block_comment_text))
        (block_comment_text
          (block_comment
            (block_comment_text))))))
(double_line)))

====================|||
Lookahead Block Comment
====================|||

---- MODULE Test ----
(************************************)
(* This comment requires lookahead
   ((* So does this one **)
   (((((* and this one *****)       *)
(************************************)
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (block_comment
    (block_comment_text
      (block_comment (block_comment_text))
      (block_comment (block_comment_text))))
(double_line)))

====================|||
Block Comment in Conjlist
====================|||

---- MODULE Test ----
op ==
  /\ 1
(* this should be ignored *)
  /\ 2
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (block_comment (block_comment_text))
      (conj_item (bullet_conj) (nat_number))
    )
  )
(double_line)))

====================|||
Block Comment in Disjlist
====================|||

---- MODULE Test ----
op ==
  \/ 1
(* this should be ignored *)
  \/ 2
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (disj_list
      (disj_item (bullet_disj) (nat_number))
      (block_comment (block_comment_text))
      (disj_item (bullet_disj) (nat_number))
    )
  )
(double_line)))

====================|||
Fancy Block Comment
====================|||

---- MODULE Test ----
(************************************)
(* Lorem ipsum dolor sit amet,      *)
(* consectetur adipiscing elit. In  *)
(* ultricies odio tellus, sed       *)
(* interdum metus vulputate nec.    *)
(* Lorem ipsum dolor sit amet,      *)
(* consectetur adipiscing elit.     *)
(************************************)
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (block_comment (block_comment_text))
(double_line)))

====================|||
Multiple Fancy Block Comments
====================|||

---- MODULE Test ----
  (************************************)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit. In  *)
  (* ultricies odio tellus, sed       *)
  (* interdum metus vulputate nec.    *)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit.     *)
  (************************************)
op == x
  (************************************)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit. In  *)
  (* ultricies odio tellus, sed       *)
  (* interdum metus vulputate nec.    *)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit.     *)
  (************************************)
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (block_comment (block_comment_text))
  (operator_definition (identifier) (def_eq) (identifier_ref))
  (block_comment (block_comment_text))
(double_line)))

====================|||
Sequential Nested Block Comments
====================|||

---- MODULE Test ----
(* text *)    (* text (* text *)*)(* text *)
(* text *)
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (block_comment 
    (block_comment_text
      (block_comment
        (block_comment_text))))
(double_line)))

====================|||
Block Comments Separated By Single Line
====================|||

---- MODULE Test ----
  (************************************)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit. In  *)
  (* ultricies odio tellus, sed       *)
  (* interdum metus vulputate nec.    *)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit.     *)
  (************************************)
  (************************************)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit. In  *)
  (* ultricies odio tellus, sed       *)
  (* interdum metus vulputate nec.    *)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit.     *)
  (************************************)
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (block_comment (block_comment_text))
(double_line)))

====================|||
Block Comments Separated By Two Lines
====================|||

---- MODULE Test ----
  (************************************)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit. In  *)
  (* ultricies odio tellus, sed       *)
  (* interdum metus vulputate nec.    *)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit.     *)
  (************************************)

  (************************************)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit. In  *)
  (* ultricies odio tellus, sed       *)
  (* interdum metus vulputate nec.    *)
  (* Lorem ipsum dolor sit amet,      *)
  (* consectetur adipiscing elit.     *)
  (************************************)
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (block_comment (block_comment_text))
  (block_comment (block_comment_text))
(double_line)))

====================|||
Block Comment With Nested Line Comment
====================|||

---- MODULE Test ----
  (* \* *)
====

--------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (block_comment (block_comment_text))
(double_line)))

