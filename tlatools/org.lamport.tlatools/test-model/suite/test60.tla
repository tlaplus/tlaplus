-------------------- MODULE test60 --------------------
(***************************************************************************)
(* Test of handling strings as sequences.                                  *)
(***************************************************************************)

EXTENDS Sequences, TLC

ASSUME "abc" \o "def" = "abcdef"
ASSUME Len("abcdef") = 6
ASSUME "a\\b\"c\nd" = "a\\b\"" \o "c\nd" 
ASSUME Len("a\\b\"c\nd") = 7

========================================

