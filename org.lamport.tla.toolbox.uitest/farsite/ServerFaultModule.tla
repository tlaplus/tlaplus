---- MODULE ServerFaultModule ----
(*`^\addcontentsline{toc}{section}{ServerFaultModule}^'*)

EXTENDS ServerMessageModule
(* ********** Definitions ************************************************************************************************** *)

VARIABLE Corrupted

(*Defn*)CorruptedType==Boolean

(*Defn*)CorruptedInit==FALSE

(* ********** Partial Actions ********************************************************************************************** *)

(*Defn*)NoChangeToCorruption==UNCHANGED Corrupted

(* ********** Actions ****************************************************************************************************** *)

(*Defn*)CorruptThisServer==
  /\ (\neg Corrupted)
  /\ (Corrupted')=TRUE
  /\ SignNoCertificate
  /\ SendNoMessage

(*Defn*)SendArbitraryMessage==
  /\ Corrupted
  /\ UNCHANGED Corrupted
  /\ SignNoCertificate
  /\ ( \E dest \in Host,msg \in CommonMessage \union ServerMessage:
          SendMessage(dest,msg))

(*Defn*)SignArbitraryCertificate==
  /\ Corrupted
  /\ UNCHANGED Corrupted
  /\ SendNoMessage
  /\ (\E cert \in Certificate:SignCertificate(cert))
====
