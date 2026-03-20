--------------------------- MODULE LiveHourClock ----------------------------
(***************************************************************************)
(* This module adds the liveness condition to the hour clock specification *)
(* of module HourClock.                                                    *)
(***************************************************************************)

EXTENDS HourClock, TLC, TLCExt

LSpec == HC /\ WF_hr(HCnxt)
  (*************************************************************************)
  (* The specification with the liveness condition conjoined.              *)
  (*************************************************************************)

(***************************************************************************)
(* We now define some properties that LSpec satisfies.                     *)
(***************************************************************************)
AlwaysTick == []<><<HCnxt>>_hr
  (*************************************************************************)
  (* Asserts that infinitely many <<HCnxt>>_hr steps occur.                *)
  (*************************************************************************)

AllTimes == \A n \in 1..12 : []<>(hr = n)
  (*************************************************************************)
  (* Asserts that, for each time n in 1..12, hr infinitely often equals n. *)
  (*************************************************************************)

TypeInvariance == []HCini
  (*************************************************************************)
  (* The temporal formula asserting that HCini is always true.  It is      *)
  (* stated in this way to show you another way of telling TLC to check an *)
  (* invariant.                                                            *)
  (*************************************************************************)
  
-----------------------------------------------------------------------------
THEOREM  LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance

ClockSettles == \E n \in 1..12 : <>[](hr = n)

PostCondition ==
   CounterExample =
    [ action |->
      { << <<1, [hr |-> 1]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<2, [hr |-> 2]>> >>,
        << <<2, [hr |-> 2]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<3, [hr |-> 3]>> >>,
        << <<3, [hr |-> 3]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<4, [hr |-> 4]>> >>,
        << <<4, [hr |-> 4]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<5, [hr |-> 5]>> >>,
        << <<5, [hr |-> 5]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<6, [hr |-> 6]>> >>,
        << <<6, [hr |-> 6]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<7, [hr |-> 7]>> >>,
        << <<7, [hr |-> 7]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<8, [hr |-> 8]>> >>,
        << <<8, [hr |-> 8]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<9, [hr |-> 9]>> >>,
        << <<9, [hr |-> 9]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<10, [hr |-> 10]>> >>,
        << <<10, [hr |-> 10]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<11, [hr |-> 11]>> >>,
        << <<11, [hr |-> 11]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<12, [hr |-> 12]>> >>,
        << <<12, [hr |-> 12]>>,
           [ name |-> "HCnxt",
             location |->
                 [ beginLine |-> 5,
                   beginColumn |-> 12,
                   endLine |-> 5,
                   endColumn |-> 46,
                   module |-> "HourClock" ] ],
           <<1, [hr |-> 1]>> >> },
  state |->
      { <<1, [hr |-> 1]>>,
        <<2, [hr |-> 2]>>,
        <<3, [hr |-> 3]>>,
        <<4, [hr |-> 4]>>,
        <<5, [hr |-> 5]>>,
        <<6, [hr |-> 6]>>,
        <<7, [hr |-> 7]>>,
        <<8, [hr |-> 8]>>,
        <<9, [hr |-> 9]>>,
        <<10, [hr |-> 10]>>,
        <<11, [hr |-> 11]>>,
        <<12, [hr |-> 12]>> } ]
=============================================================================

