----------------------- MODULE Github1524MissingLabel -----------------------
EXTENDS Sequences
(* --algorithm Missing {
variables hit = FALSE;
procedure NoOp() {
  Body:
    return;
}
process (A = 1) {
  Start:
    call NoOp();
    goto Violaton;  \* Typo: should be Violation.
  Violation:
    hit := TRUE;
}
process (B = 2) {
  Loop:
    skip;
    goto Loop;
}
} *)
\* Violation sets hit to TRUE. The call-goto names Violaton.
\* Process B loops, so A can sit at that name while TLC reports no error.
Inv == hit = FALSE
====
