----------------------------- MODULE RealTime -------------------------------
(***************************************************************************)
(* This standard module is described in Chapter 9 of the book "Specifying  *)
(* Systems".  The type of specification described there cannot be handled  *)
(* by the TLC model checker.                                               *)
(***************************************************************************)
EXTENDS Reals 
VARIABLE now

RTBound(A, v, D, E) == 
  LET TNext(t)  ==  t' = IF <<A>>_v \/ ~(ENABLED <<A>>_v)'
                           THEN 0 
                           ELSE t + (now'-now)

      Timer(t) == (t=0)  /\  [][TNext(t)]_<<t, v, now>>

      MaxTime(t) == [](t \leq E) 

      MinTime(t) == [][A => t \geq D]_v 
  IN \EE t : Timer(t) /\ MaxTime(t) /\ MinTime(t)
-----------------------------------------------------------------------------
RTnow(v) == LET NowNext == /\ now' \in {r \in Real : r > now} 
                           /\ UNCHANGED v
            IN  /\ now \in Real 
                /\ [][NowNext]_now
                /\ \A r \in Real : WF_now(NowNext /\ (now'>r))
=============================================================================
