---- MODULE MessengerModule ----
(*`^\addcontentsline{toc}{section}{MessengerModule}^'*)

EXTENDS Sequences,PhysicalComponentsModule
(* ********** Definitions ************************************************************************************************** *)

(*Defn*)AddressedMessage==[destination:Host,message:Blob]
(*Defn*)MakeAddressedMessage(i_destination,i_message)==
  [destination|->i_destination,message|->i_message]

(*Defn*)AddressedMessageSet==SUBSET AddressedMessage

(*Defn*)HostAddressedMessageSetsToSendType==[Host->AddressedMessageSet]

(*Defn*)HostMessageReceiptDecisionsType==[Host->NilOr(Host)]

(*Defn*)HostIncomingMessageQueuesType==[Host->[Host->BlobSeq]]

(*Defn*)HostAddressedMessageSetsToSendInit==[source \in Host|->{}]

(*Defn*)HostMessageReceiptDecisionsInit==[dest \in Host|->Nil]

(*Defn*)HostIncomingMessageQueuesInit==
  [dest \in Host|->[source \in Host|-><<>>]]

VARIABLE HostAddressedMessageSetsToSend

VARIABLE HostMessageReceiptDecisions

VARIABLE HostIncomingMessageQueues

(* ********** Predicates *************************************************************************************************** *)

(*Defn*)MessengerInitialized==
  /\ HostAddressedMessageSetsToSend=HostAddressedMessageSetsToSendInit
  /\ HostMessageReceiptDecisions=HostMessageReceiptDecisionsInit
  /\ HostIncomingMessageQueues=HostIncomingMessageQueuesInit

(* ********** Actions ****************************************************************************************************** *)

(*Defn*)UpdateMessageQueues==
  \E hostAddressedMessageSetsToSend \in HostAddressedMessageSetsToSendType,
     hostMessageReceiptDecisions \in HostMessageReceiptDecisions
     :
     LET
       (*Defn*)newIncomingMessageSequences==
         [dest \in Host|->
           [source \in Host|->
             CHOOSE msgSeq \in BlobSeq:
               IsSequenceOfSetElements(
                 msgSeq,
                 {msg \in Blob:
                   ( \E adrMsg \in hostAddressedMessageSetsToSend[source]:
                        /\ adrMsg.destination=dest
                        /\ adrMsg.message=msg)
                 })
           ]
         ]
       (*Defn*)oldIncomingMessageSequences==
         [dest \in Host|->
           [source \in Host|->
             IF
               /\ Len((HostIncomingMessageQueues[dest])[source])\geq 1
               /\ hostMessageReceiptDecisions[dest]=source
             THEN
               AllButFirst((HostIncomingMessageQueues[dest])[source])
             ELSE
               (HostIncomingMessageQueues[dest])[source]
           ]
         ]
     IN
       /\ (HostAddressedMessageSetsToSend')=hostAddressedMessageSetsToSend
       /\ (HostMessageReceiptDecisions')=hostMessageReceiptDecisions
       /\ (HostIncomingMessageQueues')=
          [dest \in Host|->
            [source \in Host|->
              ((oldIncomingMessageSequences[dest])[source])\o
              ( (newIncomingMessageSequences[dest])[source])
            ]
          ]
====
