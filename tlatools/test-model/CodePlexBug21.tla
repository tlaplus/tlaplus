--------------------------- MODULE CodePlexBug21 ---------------------------
EXTENDS Naturals, TLC

func1 == [x \in 1..3 |-> x]
func2 == <<1,2,3>>

ASSUME func1 = func2 \* evaluated to TRUE
ASSUME 3 :> 11 @@ func1 = <<1,2,11>> \* evaluated to TRUE

ASSUME 3 :> 11 @@ func2 = <<1,2,11>> \* erroneously evaluated to FALSE

ASSUME 4 :> 11 @@ func2 = <<1,2,3,11>> \* throws a TLC error
=============================================================================
