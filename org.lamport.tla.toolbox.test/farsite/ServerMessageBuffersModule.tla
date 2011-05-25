---- MODULE ServerMessageBuffersModule ----
(*`^\addcontentsline{toc}{section}{ServerMessageBuffersModule}^'*)

EXTENDS ServerFileOwnershipModule
(* ********** Message Buffer Definitions *********************************************************************************** *)

(*Defn*)ConsistencyMessageBufferType==[Client->ClientConsistencyMessageSeq]

(*Defn*)ConsistencyMessageBufferInit==[client \in Client|-><<>>]

VARIABLE ConsistencyMessageBuffer

(*Defn*)LeaseRequestMessageBufferType==[Client->LeaseRequestMessageSet]

(*Defn*)LeaseRequestMessageBufferInit==[client \in Client|->{}]

VARIABLE LeaseRequestMessageBuffer

(*Defn*)InterlockMessageBufferType==[Server->ServerInterlockMessageSet]

(*Defn*)InterlockMessageBufferInit==[server \in Server|->{}]

VARIABLE InterlockMessageBuffer

(* ********** Consistency Message Buffer Predicates ************************************************************************ *)

(*Defn*)MessageInClientConsistencyBuffer(msg,sender)==
  \E index \in 1..Len(ConsistencyMessageBuffer[sender]):
     LET
       (*Defn*)destinationFile==
         IF msg \in OperationMessage
         THEN
           msg[msg.destinationField]
         ELSE
           msg.fileField.fileID
     IN
       /\ (ConsistencyMessageBuffer[sender])[index]=msg
       /\ ServerOwnsFile(thisHost,destinationFile)
       /\ (\neg NowLaterThan(msg.expiration))
       /\ ( \A i \in 1..(index-1):
               ( \neg MessagesAreOrderDependent(msg,(ConsistencyMessageBuffer[sender])[i])))

(* ********** Consistency Message Buffer Partial Actions ******************************************************************* *)

(*Defn*)DequeueClientConsistencyMessage(msg,sender)==
  /\ MessageInClientConsistencyBuffer(msg,sender)
  /\ ( \E index \in 1..Len(ConsistencyMessageBuffer[sender]):
          /\ (ConsistencyMessageBuffer[sender])[index]=msg
          /\ (ConsistencyMessageBuffer')=
             [ConsistencyMessageBuffer EXCEPT![sender]=DeleteElement(@,index)])

(*Defn*)ExpireClientConsistencyMessage(msg,sender)==
  /\ MessageInClientConsistencyBuffer(msg,sender)
  /\ ( \E index \in 1..Len(ConsistencyMessageBuffer[sender]):
          /\ (ConsistencyMessageBuffer[sender])[index]=msg
          /\ (ConsistencyMessageBuffer')=
             [ConsistencyMessageBuffer EXCEPT
               ![sender][index].expiration=BeforeTimeBegins
             ])

(*Defn*)NoChangeToConsistencyMessageBuffer==
  UNCHANGED ConsistencyMessageBuffer

(* ********** Consistency Message Buffer Actions *************************************************************************** *)

(*Defn*)BufferBatchUpdateMessage==
  \E sender \in Client,msg \in BatchUpdateMessage:
     /\ ReceiveMessage(sender,msg)
     /\ SendNoMessage
     /\ (ConsistencyMessageBuffer')=
        [ConsistencyMessageBuffer EXCEPT![sender]=(@\o msg.batch)]
     /\ UNCHANGED LeaseRequestMessageBuffer
     /\ UNCHANGED InterlockMessageBuffer

(*Defn*)DiscardMessagesFromConsistencyBuffer==
  \E client \in Client,
     keepMessages \in ClientConsistencyMessageSeq,
     nackMessages \in ClientConsistencyMessageSeq,
     keepIndices \in NatSeq,
     nackIndices \in NatSeq,
     ackIDSet \in AcknowledgementIDSet
     :
     /\ IsSequenceInterleaving(
          ConsistencyMessageBuffer[client],
          keepMessages,
          nackMessages,
          keepIndices,
          nackIndices)
     /\ nackMessages#<<>>
     /\ ( \A i \in DOMAIN ConsistencyMessageBuffer[client]:
             ( \E j \in 1..(i-1):
                  /\ IsElementInSeq(j,nackIndices)
                  /\ MessagesAreOrderDependent(
                       (ConsistencyMessageBuffer[client])[j],(ConsistencyMessageBuffer[client])[i]))
             =>
             IsElementInSeq(i,nackIndices))
     /\ ( \A i \in DOMAIN nackIndices:
             LET
               (*Defn*)nackMessage==(ConsistencyMessageBuffer[client])[(nackIndices[i])]
             IN
               \/ ( \neg
                    ServerOwnsFile(
                      thisHost,ClientConsistencyMessage_destinationFile(nackMessage)))
               \/ NowLaterThan(nackMessage.expiration)
               \/ ( \E j \in 1..(nackIndices[(i-1)]):
                       MessagesAreOrderDependent(
                         (ConsistencyMessageBuffer[client])[j],
                         (ConsistencyMessageBuffer[client])[i])))
     /\ Cardinality(ackIDSet)=Len(nackMessages)
     /\ ( \A ackID \in ackIDSet:
             ( \E i \in DOMAIN nackMessages:nackMessages[i].ackID=ackID))
     /\ LET
          (*Defn*)relevantDeeds==
            {deed \in IssuedDeeds:
              ( \E i \in DOMAIN nackMessages:
                   FileGroupIncludesFile(
                     deed.fileGroup,ClientConsistencyMessage_destinationFile(nackMessages[i])))
            }
          (*Defn*)addressedFONMessages==
            {MakeAddressedMessage(client,MakeFileOwnershipNotificationMessage(deed)):
              deed \in relevantDeeds
            }
        IN
          SendAddressedMessageSet(
            addressedFONMessages \union
            {MakeAddressedMessage(client,MakeNegativeAcknowledgementMessage(ackIDSet))})
     /\ ReceiveNoMessage
     /\ (ConsistencyMessageBuffer')=
        [ConsistencyMessageBuffer EXCEPT![client]=keepMessages]
     /\ UNCHANGED LeaseRequestMessageBuffer
     /\ UNCHANGED InterlockMessageBuffer

(* ********** Lease Message Buffer Predicates ****************************************************************************** *)

(*Defn*)MessageInLeaseRequestBuffer(msg)==
  \E requester \in Client:
     /\ msg \in LeaseRequestMessageBuffer[requester]
     /\ ServerOwnsFile(thisHost,msg.fileID)
     /\ ( \/ ( /\ FileHasBeenConceived(msg.fileID)
               /\ (\neg FileHasBeenBorrowed(msg.fileID)))
          \/ FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester))

(* ********** Lease Message Buffer Partial Actions ************************************************************************* *)

(*Defn*)ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdraw)==
  /\ msg \in LeaseRequestMessageBuffer[requester]
  /\ ServerOwnsFile(thisHost,msg.fileID)
  /\ ( \/ ( /\ FileHasBeenConceived(msg.fileID)
            /\ (\neg FileHasBeenBorrowed(msg.fileID)))
       \/ FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester))
  /\ IF withdraw
     THEN
       (LeaseRequestMessageBuffer')=
       [LeaseRequestMessageBuffer EXCEPT![requester]=(@\ {msg})]
     ELSE
       UNCHANGED LeaseRequestMessageBuffer

(*Defn*)NoChangeToLeaseRequestMessageBuffer==
  UNCHANGED LeaseRequestMessageBuffer

(* ********** Lease Message Buffer Actions ********************************************************************************* *)

(*Defn*)BufferLeaseRequestMessage==
  \E sender \in Client,msg \in LeaseRequestMessage:
     /\ ReceiveMessage(sender,msg)
     /\ SendNoMessage
     /\ (LeaseRequestMessageBuffer')=
        [LeaseRequestMessageBuffer EXCEPT![sender]=(@\union{msg})]
     /\ UNCHANGED ConsistencyMessageBuffer
     /\ UNCHANGED InterlockMessageBuffer

(*Defn*)RejectMessagesFromLeaseRequestBuffer==
  \E client \in Client,msgSet \in LeaseRequestMessageSet:
     /\ msgSet \subseteq LeaseRequestMessageBuffer[client]
     /\ (\A msg \in msgSet:(\neg ServerOwnsFile(thisHost,msg.fileID)))
     /\ LET
          (*Defn*)relevantDeeds==
            {deed \in IssuedDeeds:
              (\E msg \in msgSet:FileGroupIncludesFile(deed.fileGroup,msg.fileID))
            }
          (*Defn*)addressedFONMessages==
            {MakeAddressedMessage(client,MakeFileOwnershipNotificationMessage(deed)):
              deed \in relevantDeeds
            }
        IN
          SendAddressedMessageSet(addressedFONMessages)
     /\ ReceiveNoMessage
     /\ (LeaseRequestMessageBuffer')=
        [LeaseRequestMessageBuffer EXCEPT![client]=(@\ msgSet)]
     /\ UNCHANGED ConsistencyMessageBuffer
     /\ UNCHANGED InterlockMessageBuffer

(*Defn*)DiscardMessagesFromLeaseRequestBuffer==
  \E client \in Client,msgSet \in LeaseRequestMessageSet:
     /\ msgSet \subseteq LeaseRequestMessageBuffer[client]
     /\ ( \A msg \in msgSet:
             /\ ServerOwnsFile(thisHost,msg.fileID)
             /\ (FileHasBeenConceived(msg.fileID)=>FileHasBeenBorrowed(msg.fileID))
             /\ (\neg FileHasBeenTransitivelyBorrowedByClient(msg.fileID,client)))
     /\ SendNoMessage
     /\ ReceiveNoMessage
     /\ (LeaseRequestMessageBuffer')=
        [LeaseRequestMessageBuffer EXCEPT![client]=(@\ msgSet)]
     /\ UNCHANGED ConsistencyMessageBuffer
     /\ UNCHANGED InterlockMessageBuffer

(* ********** Interlock Message Buffer Predicates ************************************************************************** *)

(*Defn*)MessageInServerInterlockBuffer(msg)==
  \E sender \in Server:
     /\ msg \in InterlockMessageBuffer[sender]
     /\ ServerOwnsFile(thisHost,msg.destFile)
     /\ (SIMDeadline \in DOMAIN msg=>(\neg NowLaterThan(msg.deadline)))
     /\ ( \/ ServerOverseesFile(sender,msg.srcFile)
          \/ sender=OwnershipAuthorizingServer)

(* ********** Interlock Message Buffer Partial Actions ********************************************************************* *)

(*Defn*)WithdrawServerInterlockMessageSet(msgSet)==
  /\ (\A msg \in msgSet:MessageInServerInterlockBuffer(msg))
  /\ (InterlockMessageBuffer')=
     [server \in Server|->InterlockMessageBuffer[server]\ msgSet]

(*Defn*)NoChangeToInterlockMessageBuffer==UNCHANGED InterlockMessageBuffer

(* ********** Interlock Message Buffer Actions ***************************************************************************** *)

(*Defn*)BufferServerInterlockMessage==
  \E sender \in Server,msg \in ServerInterlockMessage:
     /\ ReceiveMessage(sender,msg)
     /\ SendNoMessage
     /\ (InterlockMessageBuffer')=
        [InterlockMessageBuffer EXCEPT![sender]=(@\union{msg})]
     /\ UNCHANGED ConsistencyMessageBuffer
     /\ UNCHANGED LeaseRequestMessageBuffer

(*Defn*)ManageMessageInInterlockBuffer==
  \E sender \in Server,
     msg \in ServerInterlockMessage,
     srcOverseers \in ServerSet,
     srcOwner \in Server
     :
     /\ msg \in InterlockMessageBuffer[sender]
     /\ ServerOwnsFile(srcOwner,msg.srcFile)
     /\ IF \neg ServerOverseesFile(thisHost,msg.destFile)
        THEN
          /\ SendNoMessage
          /\ ReceiveNoMessage
          /\ UNCHANGED ConsistencyMessageBuffer
          /\ UNCHANGED LeaseRequestMessageBuffer
          /\ (InterlockMessageBuffer')=[InterlockMessageBuffer EXCEPT![sender]=(@\ {msg})]
        ELSE IF
          /\ (\neg ServerOverseesFile(sender,msg.srcFile))
          /\ sender#OwnershipAuthorizingServer
        THEN
          /\ SendMessage(srcOwner,MakeFileOwnershipQueryMessage(msg.srcFile))
          /\ ReceiveNoMessage
          /\ UNCHANGED ConsistencyMessageBuffer
          /\ UNCHANGED LeaseRequestMessageBuffer
          /\ UNCHANGED InterlockMessageBuffer
        ELSE IF
          \E delegate \in Server:IssuedFileOwnershipToServer(msg.destFile,delegate)
        THEN
          \E delegate \in Server,deed \in IssuedDeeds:
             /\ IssuedFileOwnershipToServer(msg.destFile,delegate)
             /\ FileGroupIncludesFile(deed.fileGroup,msg.destFile)
             /\ SendAddressedMessageSet(
                  {
                  MakeAddressedMessage(delegate,msg),
                  MakeAddressedMessage(srcOwner,MakeFileOwnershipNotificationMessage(deed))
                  })
             /\ ReceiveNoMessage
             /\ UNCHANGED ConsistencyMessageBuffer
             /\ UNCHANGED LeaseRequestMessageBuffer
             /\ (InterlockMessageBuffer')=[InterlockMessageBuffer EXCEPT![sender]=(@\ {msg})]
        ELSE
          /\ SIMDeadline \in DOMAIN msg
          /\ NowLaterThan(msg.deadline)
          /\ ReceiveNoMessage
          /\ UNCHANGED ConsistencyMessageBuffer
          /\ UNCHANGED LeaseRequestMessageBuffer
          /\ (InterlockMessageBuffer')=[InterlockMessageBuffer EXCEPT![sender]=(@\ {msg})]
          /\ IF msg \in ParentFieldReservedMessage
             THEN
               SendMessage(
                 srcOwner,MakeUnreserveParentFieldMessage(msg.srcFile,msg.destFile))
             ELSE IF msg \in ChildFieldReservedMessage
             THEN
               SendMessage(
                 srcOwner,MakeUnreserveChildFieldMessage(msg.srcFile,msg.destFile,msg.label))
             ELSE
               SendNoMessage
====
