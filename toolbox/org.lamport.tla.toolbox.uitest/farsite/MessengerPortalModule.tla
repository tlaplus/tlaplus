---- MODULE MessengerPortalModule ----
(*`^\addcontentsline{toc}{section}{MessengerPortalModule}^'*)

EXTENDS PhysicalComponentsModule
VARIABLE AddressedMessageSetToSend

VARIABLE MessageReceiptDecision

VARIABLE IncomingMessageQueues

(*Defn*)MakeAddressedMessage(dest,msg)==[destination|->dest,message|->msg]

(*Defn*)SendAddressedMessageSet(adrMsgSet)==
  (AddressedMessageSetToSend')=adrMsgSet

(*Defn*)SendMessage(dest,msg)==
  SendAddressedMessageSet({MakeAddressedMessage(dest,msg)})

(*Defn*)SendNoMessage==(AddressedMessageSetToSend')={}

(*Defn*)ReceiveMessage(source,msg)==
  /\ Len(IncomingMessageQueues[source])\geq 1
  /\ First(IncomingMessageQueues[source])=msg
  /\ (MessageReceiptDecision')=source

(*Defn*)ReceiveNoMessage==(MessageReceiptDecision')=Nil
====
