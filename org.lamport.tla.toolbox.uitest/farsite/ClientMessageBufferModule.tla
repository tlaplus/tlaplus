---- MODULE ClientMessageBufferModule ----
(*`^\addcontentsline{toc}{section}{ClientMessageBufferModule}^'*)

EXTENDS HostBaseModule
(* ********** Definitions ************************************************************************************************** *)

(*Defn*)LeaseRecallMessageBufferType==[Server->LeaseRecallMessageSet]

(*Defn*)LeaseRecallMessageBufferInit==[server \in Server|->{}]

VARIABLE LeaseRecallMessageBuffer

(* ********** Partial Actions ********************************************************************************************** *)

(*Defn*)WithdrawLeaseRecallMessage(msg,sender)==
  /\ msg \in LeaseRecallMessageBuffer[sender]
  /\ (LeaseRecallMessageBuffer')=
     [LeaseRecallMessageBuffer EXCEPT![sender]=(@\ {msg})]

(*Defn*)NoChangeToLeaseRecallMessageBuffer==
  UNCHANGED LeaseRecallMessageBuffer

(* ********** Actions ****************************************************************************************************** *)

(*Defn*)BufferLeaseRecallMessage==
  \E sender \in Server,msg \in LeaseRecallMessage:
     /\ ReceiveMessage(sender,msg)
     /\ IF \neg ServerOwnsFile(sender,msg.fileField.fileID)
        THEN
          UNCHANGED LeaseRecallMessageBuffer
        ELSE
          (LeaseRecallMessageBuffer')=
          [LeaseRecallMessageBuffer EXCEPT![sender]=(@\union{msg})]
====
