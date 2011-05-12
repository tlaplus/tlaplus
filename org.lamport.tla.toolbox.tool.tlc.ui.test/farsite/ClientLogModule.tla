---- MODULE ClientLogModule ----
(*`^\addcontentsline{toc}{section}{ClientLogModule}^'*)

EXTENDS HostBaseModule,ClientLeasePredicatesModule
(* TODO:  To accurately reflect our intended implementation, the log should perform compression. *)

(*Defn*)LogEntry==
  [
    msg:ClientConsistencyMessage,
    submitSerNum:OpenActionSerialNumber,
    submitTime:OpenTime,
    sentTo:NilOr(Server)
  ]

(*Defn*)LogEntrySeq==ArbSeq(LogEntry)

(*Defn*)MessageLogType==LogEntrySeq

(*Defn*)MessageLogInit== <<>>

VARIABLE MessageLog

(* ********** Ancillary Operators ****************************************************************************************** *)

(*Defn*)ExpirationTimeForIndexedOperation(index)==
  MinElement(
    {
    ReadOrWriteExpirationTimeOfFileSingletonFieldSet(
      FileSingletonFieldsPeekedByOperationMessage(MessageLog[index].msg),
      MessageLog[index].sumbitSerNum,
      MessageLog[index].submitTime),
    WriteExpirationTimeOfFileSingletonFieldSet(
      FileSingletonFieldsPokedByOperationMessage(MessageLog[index].msg),
      MessageLog[index].sumbitSerNum,
      MessageLog[index].submitTime)
    })

(*Defn*)ExpirationTimeForIndexedLeaseRelease(index)==
  IndividualExpirationTimeOfFileSingletonFieldSet(
    FileSingletonFieldsPokedByLeaseReleaseMessage(MessageLog[index].msg),
    MessageLog[index].msg.rw,
    MessageLog[index].sumbitSerNum,
    MessageLog[index].submitTime)

(*Defn*)ExpirationTimeForIndexedMessage(index)==
  IF MessageLog[index].msg \in OperationMessage
  THEN
    ExpirationTimeForIndexedOperation(index)
  ELSE
    ExpirationTimeForIndexedLeaseRelease(index)

(*Defn*)MessageSetYieldsLogEntrySequence(msgSet,logEntrySeq)==
  /\ Len(logEntrySeq)=Cardinality(msgSet)
  /\ ( \A msg \in msgSet:
          ( \E i \in DOMAIN logEntrySeq:
               ( \A field \in DOMAIN(msg \ {CCMAckIDField}):
                    logEntrySeq[i].msg[field]=msg[field])))
  /\ ( \A i \in DOMAIN logEntrySeq:
          /\ logEntrySeq[i].msg.ackID \in AcknowledgementID
          /\ logEntrySeq[i].submitSerNum=ActionSerialNumber
          /\ logEntrySeq[i].submitTime=LateClock
          /\ logEntrySeq[i].sentTo=Nil
          /\ ( \A j \in DOMAIN logEntrySeq:
                  i#j=>logEntrySeq[i].msg.ackID#logEntrySeq[j].msg.ackID)
          /\ ( \A j \in DOMAIN MessageLog:logEntrySeq[i].msg.ackID#MessageLog[j].msg.ackID))

(*Defn*)IndexedOperationMessagesAreForwardDependent(index1,index2)==
  MessagesAreForwardDependent(MessageLog[index1].msg,MessageLog[index2].msg)

(*Defn*)
IndexedOperationMessagesAreTransitivelyForwardDependent(
  startOpIndex,endOpIndex)==
  \E dependentIndices \in SUBSET DOMAIN MessageLog:
     /\ endOpIndex \in dependentIndices
     /\ ( \A laterIndex \in(startOpIndex+1)..endOpIndex:
             /\ MessageLog[laterIndex].msg \in OperationMessage
             /\ ( \E earlierIndex \in startOpIndex..(laterIndex-1):
                     /\ earlierIndex \in{startOpIndex}\union dependentIndices
                     /\ IndexedOperationMessagesAreForwardDependent(earlierIndex,laterIndex))
             =>
             laterIndex \in dependentIndices)
     /\ ( \A laterIndex \in dependentIndices:
             /\ laterIndex>startOpIndex
             /\ MessageLog[laterIndex].msg \in OperationMessage
             /\ ( \E earlierIndex \in{startOpIndex}\union dependentIndices:
                     /\ earlierIndex<laterIndex
                     /\ IndexedOperationMessagesAreForwardDependent(earlierIndex,laterIndex)))

(*Defn*)IndexedOperationMessageIsTenuous(opIndex)==
  \E expOpIndex \in DOMAIN MessageLog:
     /\ MessageLog[expOpIndex].msg \in OperationMessage
     /\ (\neg NowEarlierThan(ExpirationTimeForIndexedOperation(expOpIndex)))
     /\ IndexedOperationMessagesAreTransitivelyForwardDependent(expOpIndex,opIndex)

(*Defn*)FileFieldSVLeaseSuspended(fileID,field)==
  \E opIndex \in DOMAIN MessageLog:
     /\ MessageLog[opIndex].msg \in OperationMessage
     /\ IndexedOperationMessageIsTenuous(opIndex)
     /\ MakeFileSharedValueField(fileID,field)\in
        FileSingletonFieldsPokedByOperationMessage(MessageLog[opIndex].msg)
     /\ ( \A lrIndex \in DOMAIN MessageLog:
             lrIndex>opIndex=>
             \/ MessageLog[lrIndex].msg \notin LeaseReleaseMessage
             \/ MakeFileSharedValueField(fileID,field)\notin
                FileSingletonFieldsPokedByLeaseReleaseMessage(MessageLog[lrIndex].msg))

(*Defn*)FileFieldChildLeaseSuspended(fileID,label)==
  \E opIndex \in DOMAIN MessageLog:
     /\ MessageLog[opIndex].msg \in OperationMessage
     /\ IndexedOperationMessageIsTenuous(opIndex)
     /\ MakeFileChildField(fileID,label)\in
        FileSingletonFieldsPokedByOperationMessage(MessageLog[opIndex].msg)
     /\ ( \A lrIndex \in DOMAIN MessageLog:
             lrIndex>opIndex=>
             \/ MessageLog[lrIndex].msg \notin LeaseReleaseMessage
             \/ MakeFileChildField(fileID,label)\notin
                FileSingletonFieldsPokedByLeaseReleaseMessage(MessageLog[lrIndex].msg))

(*Defn*)HandleOpeningSuspended(handle)==
  \E opIndex \in DOMAIN MessageLog:
     /\ MessageLog[opIndex].msg \in
        OpenFileOperationMessage \union CreateFileOperationMessage
     /\ IndexedOperationMessageIsTenuous(opIndex)
     /\ MessageLog[opIndex].msg.handle=handle

(*Defn*)HandleCleanupSuspended(handle)==
  \E opIndex \in DOMAIN MessageLog:
     /\ MessageLog[opIndex].msg \in CleanupFileOperationMessage
     /\ IndexedOperationMessageIsTenuous(opIndex)
     /\ MessageLog[opIndex].msg.handle=handle

(*Defn*)HandleClosingSuspended(handle)==
  \E opIndex \in DOMAIN MessageLog:
     /\ MessageLog[opIndex].msg \in
        CloseFileOperationMessage \union CloseAndUnlinkFileOperationMessage
     /\ IndexedOperationMessageIsTenuous(opIndex)
     /\ MessageLog[opIndex].msg.handle=handle

(* ********** Partial Actions ********************************************************************************************** *)

(*Defn*)PostMessageSetInLog(msgSet)==
  \E logEntrySeq \in LogEntrySeq:
     /\ MessageSetYieldsLogEntrySequence(msgSet,logEntrySeq)
     /\ (MessageLog')=(MessageLog \o logEntrySeq)

(*Defn*)PostMessageInLog(msg)==PostMessageSetInLog({msg})

(*Defn*)NoChangeToMessageLog==UNCHANGED MessageLog

(*Defn*)
UpdateCreateFileMessageInLogWithLeaseExtension(
  fileID,leaseTimeField,expiration)==
  \E index \in DOMAIN MessageLog:
     /\ MessageLog[index].msg \in CreateFileOperationMessage
     /\ MessageLog[index].msg.fileID=fileID
     /\ (MessageLog')=[MessageLog EXCEPT![index].msg[leaseTimeField]=expiration]

(*Defn*)
UpdateCreateFileMessageInLogWithNewBorrowedMaxSuffix(fileID,newMaxSuffix)==
  \E index \in DOMAIN MessageLog:
     /\ MessageLog[index].msg \in CreateFileOperationMessage
     /\ MessageLog[index].msg.fileID=fileID
     /\ (MessageLog')=[MessageLog EXCEPT![index].msg.borrowedMaxSuffix=newMaxSuffix]

(* ********** Actions ****************************************************************************************************** *)

(*Defn*)SendBatchUpdateFromLog==
  \E indices \in SUBSET DOMAIN MessageLog,server \in Server:
     /\ indices#{}
     /\ ( \A i \in indices:
             /\ ServerOwnsFile(
                  server,ClientConsistencyMessage_destinationFile(MessageLog[i].msg))
             /\ MessageLog[i].sentTo=Nil
             /\ ( \A j \in 1..(i-1):
                     j \notin indices=>
                     ( \neg MessagesAreOrderDependent(MessageLog[i].msg,MessageLog[j].msg)))
             /\ NowEarlierThan(ExpirationTimeForIndexedMessage(i)))
     /\ (MessageLog')=
        [i \in DOMAIN MessageLog|->
          IF i \in indices
          THEN
            LET(*Defn*)AtSymbol001==MessageLog[i]IN[AtSymbol001 EXCEPT!.sentTo=server]
          ELSE
            MessageLog[i]
        ]
     /\ ReceiveNoMessage
     /\ UNCHANGED ActiveProtectionRecords
     /\ UNCHANGED FileValueTableState
     /\ ( \E msgSeq \in ClientConsistencyMessageSeq,selectors \in NatSeq:
             /\ Len(msgSeq)=Cardinality(indices)
             /\ IsSortedSequenceOfSetElements(selectors,indices)
             /\ ( \A i \in DOMAIN selectors:
                     msgSeq[i]=
                     [MessageLog[(selectors[i])].msg EXCEPT
                       !.expiration=ExpirationTimeForIndexedMessage(selectors[i])
                     ])
             /\ SendMessage(server,MakeBatchUpdateMessage(msgSeq)))

(*Defn*)ProcessPositiveAcknowledgementMessage==
  \E sender \in Server,msg \in PositiveAcknowledgementMessage:
     /\ ReceiveMessage(sender,msg)
     /\ SendNoMessage
     /\ UNCHANGED ActiveProtectionRecords
     /\ UNCHANGED FileValueTableState
     /\ IF
          \neg
          ( \E logEntry \in LogEntry:
               /\ IsElementInSeq(logEntry,MessageLog)
               /\ logEntry.sentTo=sender
               /\ logEntry.msg.ackID=msg.ackID)
        THEN
          UNCHANGED MessageLog
        ELSE
          \E i \in DOMAIN MessageLog:
             /\ MessageLog[i].msg.ackID=msg.ackID
             /\ (MessageLog')=DeleteElement(MessageLog,i)

(*Defn*)ProcessNegativeAcknowledgementMessage==
  \E sender \in Server,msg \in NegativeAcknowledgementMessage:
     /\ ReceiveMessage(sender,msg)
     /\ SendNoMessage
     /\ UNCHANGED ActiveProtectionRecords
     /\ UNCHANGED FileValueTableState
     /\ IF
          \E ackID \in msg.ackIDSet:
             ( \neg
               ( \E logEntry \in LogEntry:
                    /\ IsElementInSeq(logEntry,MessageLog)
                    /\ logEntry.msg.ackID=ackID
                    /\ logEntry.sentTo=sender))
        THEN
          /\ UNCHANGED MessageLog
        ELSE
          /\ (MessageLog')=
             [i \in 1..Len(MessageLog)|->
               [MessageLog[i]EXCEPT
                 !.sentTo=IF MessageLog[i].msg.ackID \in msg.ackIDSet THEN Nil ELSE@
               ]
             ]

(* When an operation message in the log expires, we discard it from the log.  We also discard the transitive closure
	of operation messages that are forward-dependent upon the expired operation message.  This invalidates the FileValueTableState
	state that has been poked by the discarded operation messages, so we must immediately release the leases on all fields
	poked by by these operation messages, unless there is already such a lease-release message behind that operation message
	in the log. *)

(*Defn*)DiscardOperationMessagesFromLog==
  \E keepEntries \in LogEntrySeq,
     tossEntries \in LogEntrySeq,
     keepIndices \in NatSeq,
     tossIndices \in NatSeq
     :
     LET
       (*Defn*)createdFilesToEradicate==
         {fileID \in FileID:
           ( \E i \in DOMAIN tossEntries:
                /\ tossEntries[i].msg \in CreateFileOperationMessage
                /\ tossEntries[i].msg.fileID=fileID)
         }
       (*Defn*)fileSingletonFieldsToRelease==
         {fileSingletonField \in FileSharedValueFields \union FileChildField:
           ( /\ fileSingletonField.fileID \notin createdFilesToEradicate
             /\ ( \E i \in DOMAIN tossEntries:
                     /\ fileSingletonField \in
                        FileSingletonFieldsPokedByOperationMessage(tossEntries[i].msg)
                     /\ ( \A j \in DOMAIN MessageLog:
                             j>tossIndices[i]=>
                             \/ MessageLog[j].msg \notin LeaseReleaseMessage
                             \/ fileSingletonField \notin
                                FileSingletonFieldsPokedByLeaseReleaseMessage(tossEntries[i].msg))))
         }
       (*Defn*)closeAndUnlinkSerialNumbersToRestore==
         {serNum \in OpenActionSerialNumber:
           ( \E i \in DOMAIN tossEntries:
                /\ tossEntries[i].msg \in CloseAndUnlinkFileOperationMessage
                /\ tossEntries[i].submitSerNum=serNum)
         }
       (*Defn*)leaseReleaseMessages==
         {MakeLeaseReleaseMessage(fileSingletonField,PWrite):
           fileSingletonField \in fileSingletonFieldsToRelease
         }
       (*Defn*)fileHandlesToRestore(fileID)==
         {handle \in Handle:
           ( \E i \in DOMAIN tossEntries:
                /\ tossEntries[i].msg \in
                   CloseFileOperationMessage \union CloseAndUnlinkFileOperationMessage
                /\ tossEntries[i].msg.handle=handle)
         }
       (*Defn*)fileHandlesToRemove(fileID)==
         {handle \in Handle:
           ( \E i \in DOMAIN tossEntries:
                /\ tossEntries[i].msg \in
                   OpenFileOperationMessage \union CreateFileOperationMessage
                /\ tossEntries[i].msg.handle=handle)
         }
       (*Defn*)fileBonaFideHandlesToRestore(fileID)==
         {handle \in Handle:
           ( \E i \in DOMAIN tossEntries:
                /\ tossEntries[i].msg \in CleanupFileOperationMessage
                /\ tossEntries[i].msg.handle=handle)
         }
       (*Defn*)fileBonaFideHandlesToRemove(fileID)==
         {handle \in Handle:
           ( \E i \in DOMAIN tossEntries:
                /\ tossEntries[i].msg \in
                   OpenFileOperationMessage \union CreateFileOperationMessage
                /\ tossEntries[i].msg.handle=handle)
         }
       (*Defn*)fileModeHandlesToRestore(fileID,mode)==
         {handle \in Handle:
           ( \E i \in DOMAIN tossEntries:
                /\ tossEntries[i].msg \in CleanupFileOperationMessage
                /\ tossEntries[i].msg.handle=handle
                /\ mode \in tossEntries[i].msg.modes)
         }
       (*Defn*)fileModeHandlesToRemove(fileID,mode)==
         {handle \in Handle:
           ( \E i \in DOMAIN tossEntries:
                /\ tossEntries[i].msg \in
                   OpenFileOperationMessage \union CreateFileOperationMessage
                /\ tossEntries[i].msg.handle=handle
                /\ mode \in tossEntries[i].msg.modes)
         }
       (*Defn*)fileAccessHandlesToRestore(fileID,access)==
         {handle \in Handle:
           ( \E i \in DOMAIN tossEntries:
                /\ tossEntries[i].msg \in
                   CloseFileOperationMessage \union CloseAndUnlinkFileOperationMessage
                /\ tossEntries[i].msg.handle=handle
                /\ access \in tossEntries[i].msg.accesses)
         }
       (*Defn*)fileAccessHandlesToRemove(fileID,access)==
         {handle \in Handle:
           ( \E i \in DOMAIN tossEntries:
                /\ tossEntries[i].msg \in
                   OpenFileOperationMessage \union CreateFileOperationMessage
                /\ tossEntries[i].msg.handle=handle
                /\ access \in ModeSetToAccessSet(tossEntries[i].msg.modes))
         }
     IN
       /\ IsSequenceInterleaving(
            MessageLog,keepEntries,tossEntries,keepIndices,tossIndices)
       /\ tossEntries#<<>>
       /\ ( \A i \in DOMAIN tossEntries:
               /\ tossEntries[i].msg \in OperationMessage
               /\ tossEntries[i].sentTo=Nil)
       /\ ( \A i \in DOMAIN MessageLog:
               /\ MessageLog[i].msg \in OperationMessage
               /\ ( \E j \in 1..(i-1):
                       /\ IsElementInSeq(j,tossIndices)
                       /\ IndexedOperationMessagesAreForwardDependent(j,i))
               =>
               IsElementInSeq(i,tossIndices))
       /\ ( \A i \in DOMAIN tossIndices:
               \/ (\neg NowEarlierThan(ExpirationTimeForIndexedOperation(tossIndices[i])))
               \/ ( \E j \in 1..(tossIndices[(i-1)]):
                       IndexedOperationMessagesAreForwardDependent(j,i)))
       /\ ReceiveNoMessage
       /\ SendNoMessage
       /\ UpdateProtectionRecordsWithOperationMessageDiscard(
            createdFilesToEradicate,
            fileSingletonFieldsToRelease,
            closeAndUnlinkSerialNumbersToRestore)
       /\ (FileValueTableState')=
          [fileID \in FileID|->
            [FileValueTableState[fileID]EXCEPT
              !.openHandle.self[thisHost]=
                ((@\union fileHandlesToRestore(fileID))\ fileHandlesToRemove(fileID)),
              !.bonaFide[thisHost]=
                ( (@\union fileBonaFideHandlesToRestore(fileID))\
                  fileBonaFideHandlesToRemove(fileID)),
              !.modes=
                [mode \in DOMAIN@|->
                  IF mode \in Mode
                  THEN
                    LET
                      (*Defn*)AtSymbol002==@[mode]
                    IN
                      [AtSymbol002 EXCEPT
                        !.self[thisHost]=
                          ( (@\union fileModeHandlesToRestore(fileID,mode))\
                            fileModeHandlesToRemove(fileID,mode))
                      ]
                  ELSE
                    @[mode]
                ],
              !.accesses=
                [access \in DOMAIN@|->
                  IF access \in Access
                  THEN
                    LET
                      (*Defn*)AtSymbol003==@[access]
                    IN
                      [AtSymbol003 EXCEPT
                        ![thisHost]=
                          ( (@\union fileAccessHandlesToRestore(fileID,access))\
                            fileAccessHandlesToRemove(fileID,access))
                      ]
                  ELSE
                    @[access]
                ]
            ]
          ]
       /\ ( \E logEntrySeq \in LogEntrySeq:
               /\ MessageSetYieldsLogEntrySequence(leaseReleaseMessages,logEntrySeq)
               /\ (MessageLog')=(keepEntries \o logEntrySeq))

(*Defn*)DiscardLeaseReleaseMessageFromLog==
  \E index \in DOMAIN MessageLog:
     /\ MessageLog[index].msg \in LeaseReleaseMessage
     /\ (\neg NowEarlierThan(ExpirationTimeForIndexedLeaseRelease(index)))
     /\ ( \A i \in 1..(index-1):
             MessageLog[i].msg \in OperationMessage=>
             FileSingletonFieldsPokedByLeaseReleaseMessage(MessageLog[index].msg)
             \intersect
             FileSingletonFieldsPeekedOrPokedByOperationMessage(MessageLog[i].msg)
             =
             {})
     /\ ReceiveNoMessage
     /\ SendNoMessage
     /\ UNCHANGED ActiveProtectionRecords
     /\ UNCHANGED FileValueTableState
     /\ (MessageLog')=DeleteElement(MessageLog,index)
====
