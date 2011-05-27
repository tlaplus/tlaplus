---- MODULE ClientFaultModule ----
(*`^\addcontentsline{toc}{section}{ClientFaultModule}^'*)

EXTENDS HostBaseModule
(* ********** Definitions ************************************************************************************************** *)

VARIABLE Corrupted

(*Defn*)CorruptedType==Boolean

(*Defn*)CorruptedInit==FALSE

(* ********** Partial Actions ********************************************************************************************** *)

(*Defn*)NoChangeToCorruption==UNCHANGED Corrupted

(* ********** Actions ****************************************************************************************************** *)

(*Defn*)CorruptThisClient==
  /\ (\neg Corrupted)
  /\ (Corrupted')=TRUE
  /\ SignNoCertificate
  /\ SendNoMessage

(*Defn*)SendArbitraryMessage==
  /\ Corrupted
  /\ UNCHANGED Corrupted
  /\ SignNoCertificate
  /\ (\E dest \in Host,msg \in CommonMessage:SendMessage(dest,msg))

(*Defn*)SignArbitraryCertificate==
  /\ Corrupted
  /\ UNCHANGED Corrupted
  /\ SendNoMessage
  /\ (\E cert \in Certificate:SignCertificate(cert))
====
