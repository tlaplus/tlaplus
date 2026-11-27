----------------------- MODULE Github1524OtherProcess -----------------------
(* --algorithm OtherProcess {
procedure NoOp() {
  Body:
    return;
}
process (A = 1) {
  Start:
    call NoOp();
    goto OnlyB;
}
process (B = 2) {
  OnlyB:
    skip;
}
}
*)
====
