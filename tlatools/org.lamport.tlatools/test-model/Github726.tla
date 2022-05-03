-------------------------------- MODULE Github726 --------------------------------
EXTENDS TLC

msgs == [ a |-> [ data |-> 15 ] ]

GetMsg(dst) ==
    [ dst |-> dst ] @@ msgs[dst]

Pair ==
    LET m == GetMsg("a")
    IN <<m, m>>

ASSUME Pair[1] = Pair[2]

PrintPrintGetMsg ==
    LET m == GetMsg("a")  \* expect: [data |-> 15, dst |-> "a"]
    IN <<PrintT(m) , PrintT(m)>>

ASSUME PrintPrintGetMsg = <<TRUE, TRUE>>

=============================================================================