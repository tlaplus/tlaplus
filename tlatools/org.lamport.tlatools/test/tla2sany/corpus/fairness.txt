=====================|||
Basic Weak Fairness
=====================|||

---- MODULE Test ----
op == WF_(vars)(x)
====

---------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (fairness (parentheses (identifier_ref)) (identifier_ref))
  )
(double_line)))

=====================|||
Basic Strong Fairness
=====================|||

---- MODULE Test ----
op == SF_(vars)(x)
====

---------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (fairness (parentheses (identifier_ref)) (identifier_ref))
  )
(double_line)))

=====================|||
Weak Fairness Ambiguity
=====================|||

---- MODULE Test ----
op == WF_vars(x)
====

---------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (fairness (identifier_ref) (identifier_ref))
  )
(double_line)))

=====================|||
Strong Fairness Ambiguity
=====================|||

---- MODULE Test ----
op == SF_vars(x)
====

---------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (fairness (identifier_ref) (identifier_ref))
  )
(double_line)))

==============================|||
Fairness with Tuple Literal
==============================|||

---- MODULE Test ----
op == WF_<<x, y>>(f)
op == SF_x(f)
====

------------------------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq)
    definition: (fairness
      (tuple_literal
        (langle_bracket)
        (identifier_ref)
        (identifier_ref)
        (rangle_bracket)
      )
      (identifier_ref)
    )
  )
  (operator_definition name: (identifier) (def_eq)
    definition: (fairness (identifier_ref) (identifier_ref))
  )
(double_line)))

