------------------ MODULE Github652 -------------------
EXTENDS Naturals, TLCExt

(* Causes: "Attempted to check equality of integer 1 with non-integer" *)

\* FcnRcdValue#equals
ASSUME [ i \in {1,3} |-> FALSE] # <<1,2>>
ASSUME <<1,2>> # [ i \in {1,3} |-> FALSE]
ASSUME [ i \in 1..2 |-> i ] # [ i \in {1,3} |-> FALSE]
ASSUME [ i \in {1,2} |-> i ] # [ i \in {1,3} |-> FALSE]

\* FcnRcdValue#compareTo
ASSUME {[ i \in 1..2 |-> FALSE], [ i \in {1,3}|-> i]} # {}
ASSUME {[ i \in {1,3} |-> FALSE], [ i \in 1..2|-> i]} # {}
ASSUME {[ i \in {1,3} |-> FALSE], [ i \in {1,2} |-> i]} # {}

\* RecordValue#equals
ASSUME [a |-> 1, b |-> 1] # [a |-> TRUE, c |-> 1]

\* RecordValue#compareTo
ASSUME {[a|->1, b|->2, d|->3], [a|->1, b|->FALSE, c|->3]} # {} 
ASSUME {[a|->1, b|->FALSE, c|->3], [a|->1, b|->2, d|->3]} # {} 

ASSUME \A f \in [ {1,2} -> {1,2} ] : 
            \A g \in [ {1,3} -> BOOLEAN ] :
                f # g

--------------------------------------------------------

\* Behaves according to "Specifying Systems".

\* FcnRcdValue.java
ASSUME [ i \in 1..2 |-> i ] # [ i \in 1..3 |-> FALSE]
ASSUME [ i \in {1,2} |-> i ] # [ i \in 1..3 |-> FALSE]
ASSUME [ i \in 1..2 |-> i ] # [ i \in {1,2,3} |-> FALSE]
ASSUME [ i \in {1,2} |-> i ] # [ i \in {1,2,3} |-> FALSE]
ASSUME [ i \in 1..2 |-> i ] # [ i \in 2..3 |-> FALSE]
ASSUME [ i \in {1,2} |-> i ] # [ i \in {2,3} |-> FALSE] 

ASSUME [ i \in (1..2) |-> i ] # [ i \in 2..3 |-> FALSE]

\* RecordValue
ASSUME [a |-> 1, b |-> 1] # [a |-> TRUE, b |-> 2, c |-> 1]

\* TupleValue
ASSUME <<1,TRUE,3>> # <<1,2>>
ASSUME <<1,2>> # <<1,TRUE,3>>

========================================================

\* SetOfTupleValues.java
ASSUME {1,2} \X {TRUE} # {}
ASSUME {1,2} \X {TRUE, TRUE} # {}
ASSUME {TRUE} \X {1,2} # {}
ASSUME {TRUE,TRUE} \X {1,2} # {}

\* fail
ASSUME {1,TRUE} \X {1,2} # {}
ASSUME {1,2} \X {1,TRUE} # {}
---------------------------------------------------------

(* Below, all must fail. *)

\* SetOfRcdsValue
ASSUME AssertError("Attempted to compare boolean TRUE with non-boolean:\n1", [ a : {1, TRUE}] # {})


---- CONFIG Github652 ----
====