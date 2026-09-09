---- MODULE Github1417Variants ----
opLocal == LET Local == INSTANCE Github1417Local IN TRUE

opParam == LET Param(x) == INSTANCE Github1417Empty IN TRUE

opMixed == LET Both == INSTANCE Github1417Ops
               Nothing == INSTANCE Github1417Empty
           IN TRUE
====
