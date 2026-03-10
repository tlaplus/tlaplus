---- MODULE Github725f ----
EXTENDS Sequences, Naturals

VARIABLES outerRes, outerSeq

---- MODULE Inner725f ----
    VARIABLES res, myseq

    Step ==
        /\ res = 0
        /\ res' = 1
        /\ myseq' = SelectSeq(myseq, LAMBDA e: e /= res')

    Fairness == WF_<<res, myseq>>(Step)
====

Svc == INSTANCE Inner725f WITH res <- outerRes, myseq <- outerSeq

Init ==
    /\ outerSeq = <<1, 2, 3>>
    /\ outerRes = 0

Step ==
    \/ Svc!Step
    \/ ~ENABLED Svc!Step /\ UNCHANGED <<outerRes, outerSeq>>

Spec ==
    /\ Init
    /\ [][Step]_<<outerRes, outerSeq>>
    /\ Svc!Fairness

SpecRunsToEnd == <>[](~ENABLED Svc!Step)

====
