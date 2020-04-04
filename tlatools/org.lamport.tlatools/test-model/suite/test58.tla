------------------- MODULE test58 --------------------
\* Test of binary, octal, and hexadecimal numbers

EXTENDS Naturals

ASSUME
  /\ 63 = \b111111
  /\ 63 = \o77
  /\ 63 = \h3F
  /\ 63 = \B111111
  /\ 63 = \O77
  /\ 63 = \H3f
  /\ 63 = \H3F
  /\ 63 = \h3f

=======================================================
