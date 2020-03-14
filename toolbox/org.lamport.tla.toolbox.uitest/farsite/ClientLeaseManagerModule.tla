---- MODULE ClientLeaseManagerModule ----
(*`^\addcontentsline{toc}{section}{ClientLeaseManagerModule}^'*)

EXTENDS ClientLeaseResourcesModule
(* ********** Partial Actions ********************************************************************************************** *)

(*Defn*)LocallyExtendLease(fileField,rw)==
  IF fileField \in FileSharedValueFields \union FileChildField
  THEN
    /\ UpdateCreateFileMessageInLogWithLeaseExtension(
         fileField.fileID,CFSharedValueLeaseTime,EarlyClock+ClientShortLeaseTimeLimit)
    /\ UpdateProtectionRecordsWithLeaseGrant(
         UNION
         {
         {MakeFileSharedValueField(fileField.fileID,field):
           field \in FSharedValueFields
         },
         {MakeFileChildField(fileField.fileID,label):label \in Label}
         },
         rw,
         PIndividual,
         EarlyClock+ClientShortLeaseTimeLimit)
  ELSE IF
    /\ fileField \in FileOpenHandleField
    /\ fileField.so=BBSelf
    /\ rw=PRead
  THEN
    /\ UpdateCreateFileMessageInLogWithLeaseExtension(
         fileField.fileID,
         CFBlackBoxReadSelfLeaseTime,
         EarlyClock+ClientLongLeaseTimeLimit)
    /\ UpdateProtectionRecordsWithLeaseGrant(
         {MakeFileOpenHandleField(fileField.fileID,BBSelf)},
         rw,
         PIndividual,
         EarlyClock+ClientLongLeaseTimeLimit)
  ELSE IF
    /\ fileField \in FileOpenHandleField \union FileModeField
    /\ fileField.so=BBSelf
    /\ rw=PWrite
  THEN
    /\ UpdateCreateFileMessageInLogWithLeaseExtension(
         fileField.fileID,
         CFBlackBoxWriteSelfLeaseTime,
         EarlyClock+ClientShortLeaseTimeLimit)
    /\ UpdateProtectionRecordsWithLeaseGrant(
         UNION
         {
         {MakeFileOpenHandleField(fileField.fileID,BBSelf)},
         {MakeFileModeField(fileField.fileID,mode,BBSelf):mode \in Mode}
         },
         rw,
         PIndividual,
         EarlyClock+ClientShortLeaseTimeLimit)
  ELSE IF
    /\ fileField \in FileOpenHandleField \union FileModeField
    /\ fileField.so=BBOther
    /\ rw=PRead
  THEN
    /\ UpdateCreateFileMessageInLogWithLeaseExtension(
         fileField.fileID,
         CFBlackBoxReadOtherLeaseTime,
         EarlyClock+ClientShortLeaseTimeLimit)
    /\ UpdateProtectionRecordsWithLeaseGrant(
         UNION
         {
         {MakeFileOpenHandleField(fileField.fileID,BBOther)},
         {MakeFileModeField(fileField.fileID,mode,BBOther):mode \in Mode}
         },
         rw,
         PIndividual,
         EarlyClock+ClientShortLeaseTimeLimit)
  ELSE IF
    /\ fileField \in FileBonaFideField
    /\ rw=PRead
  THEN
    /\ UpdateCreateFileMessageInLogWithLeaseExtension(
         fileField.fileID,CFPrivateValueLeaseTime,EarlyClock+ClientLongLeaseTimeLimit)
    /\ UpdateProtectionRecordsWithLeaseGrant(
         {MakeFileBonaFideField(fileField.fileID)},
         rw,
         PIndividual,
         EarlyClock+ClientLongLeaseTimeLimit)
  ELSE
    /\ NoChangeToMessageLog
    /\ UNCHANGED ActiveProtectionRecords

(* ********** Lease Recalls ************************************************************************************************ *)

(*Defn*)ProcessSingletonLeaseRecallMessage==
  \E sender \in Server,msg \in LeaseRecallMessage:
     /\ WithdrawLeaseRecallMessage(msg,sender)
     /\ (\neg SomeOperationHasPriorityOverLeaseRecallMessage(msg))
     /\ msg.fileField \in FileSingletonField
     /\ UNCHANGED FileValueTableState
     /\ ReceiveNoMessage
     /\ SendNoMessage
     /\ IF \neg HaveIndividualLeaseOnFileSingletonField(msg.fileField,msg.rw)
        THEN
          /\ UNCHANGED ActiveProtectionRecords
          /\ NoChangeToMessageLog
        ELSE
          /\ UpdateProtectionRecordsWithLeaseRelease({msg.fileField},msg.rw)
          /\ PostMessageInLog(MakeLeaseReleaseMessage(msg.fileField,msg.rw))

(*Defn*)ProcessInfiniteChildLeaseRecallMessage==
  \E sender \in Server,msg \in LeaseRecallMessage:
     LET
       (*Defn*)fileSingletonFieldsRecalled==
         FileFieldToFileSingletonFieldSet(msg.fileField)
       (*Defn*)fileSingletonFieldsToRelease==
         {fileSingletonField \in fileSingletonFieldsRecalled:
           HaveIndividualLeaseOnFileSingletonField(fileSingletonField,PWrite)
         }
       (*Defn*)fileFieldsToRelease==
         FileSingletonFieldSetToFileFieldSet(fileSingletonFieldsToRelease)
       (*Defn*)leaseReleaseMessages==
         {MakeLeaseReleaseMessage(fileField,PWrite):fileField \in fileFieldsToRelease}
     IN
       /\ WithdrawLeaseRecallMessage(msg,sender)
       /\ (\neg SomeOperationHasPriorityOverLeaseRecallMessage(msg))
       /\ msg.fileField \in FileInfiniteChildField
       /\ UNCHANGED FileValueTableState
       /\ ReceiveNoMessage
       /\ SendNoMessage
       /\ IF leaseReleaseMessages={}
          THEN
            /\ UNCHANGED ActiveProtectionRecords
            /\ NoChangeToMessageLog
          ELSE
            /\ UpdateProtectionRecordsWithLeaseRelease(fileSingletonFieldsToRelease,PWrite)
            /\ PostMessageSetInLog(leaseReleaseMessages)

(* ********** Lease Grants ************************************************************************************************* *)

(*Defn*)ProcessSingletonLeaseGrantMessage==
  \E sender \in Server,msg \in SingletonLeaseGrantMessage:
     /\ ReceiveMessage(sender,msg)
     /\ NoChangeToMessageLog
     /\ NoChangeToLeaseRecallMessageBuffer
     /\ SendNoMessage
     /\ IF \neg ServerOwnsFile(sender,msg.fileField.fileID)
        THEN
          /\ UNCHANGED ActiveProtectionRecords
          /\ UNCHANGED FileValueTableState
        ELSE IF
          /\ (\neg msg.extension)
          /\ ( \E rw \in PReadOrWrite:
                  HaveIndividualLeaseOnFileSingletonField(msg.fileField,rw))
        THEN
          /\ UNCHANGED ActiveProtectionRecords
          /\ UNCHANGED FileValueTableState
        ELSE
          /\ UpdateProtectionRecordsWithLeaseGrant(
               {msg.fileField},msg.rw,PIndividual,msg.expiration)
          /\ IF msg.extension
             THEN
               UNCHANGED FileValueTableState
             ELSE
               (FileValueTableState')=
               IF msg.fileField \in FileSharedValueFields
               THEN
                 [FileValueTableState EXCEPT
                   ![msg.fileField.fileID][msg.fileField.field]=msg.value
                 ]
               ELSE IF msg.fileField \in FileChildField
               THEN
                 [FileValueTableState EXCEPT
                   ![msg.fileField.fileID].children[msg.fileField.label]=msg.value
                 ]
               ELSE IF
                 (msg.fileField \in FileOpenHandleField/\ msg.fileField.so=BBSelf)/\
                 msg.rw=PRead
               THEN
                 [
                   [
                     [
                       [FileValueTableState EXCEPT
                         ![msg.fileField.fileID].openHandle.self[thisHost]=msg.value
                       ]
                     EXCEPT
                       ![msg.fileField.fileID].bonaFide[thisHost]=(@\intersect msg.value)
                     ]
                   EXCEPT
                     ![msg.fileField.fileID]=
                       [@EXCEPT
                         !.modes=
                           [mode \in DOMAIN@|->
                             IF mode \in Mode
                             THEN
                               LET
                                 (*Defn*)AtSymbol001==@[mode]
                               IN
                                 [AtSymbol001 EXCEPT!.self[thisHost]=(@\intersect msg.value)]
                             ELSE
                               @[mode]
                           ]
                       ]
                   ]
                 EXCEPT
                   ![msg.fileField.fileID]=
                     [@EXCEPT
                       !.accesses=
                         [access \in DOMAIN@|->
                           IF access \in Access
                           THEN
                             LET
                               (*Defn*)AtSymbol002==@[access]
                             IN
                               [AtSymbol002 EXCEPT![thisHost]=(@\intersect msg.value)]
                           ELSE
                             @[access]
                         ]
                     ]
                 ]
               ELSE IF msg.fileField \in FileOpenHandleField/\ msg.fileField.so=BBOther
               THEN
                 [FileValueTableState EXCEPT
                   ![msg.fileField.fileID].openHandle.other[thisHost]=msg.value
                 ]
               ELSE IF msg.fileField \in FileBonaFideField
               THEN
                 [
                   [FileValueTableState EXCEPT
                     ![msg.fileField.fileID].bonaFide[thisHost]=msg.value
                   ]
                 EXCEPT
                   ![msg.fileField.fileID]=
                     [@EXCEPT
                       !.modes=
                         [mode \in DOMAIN@|->
                           IF mode \in Mode
                           THEN
                             LET
                               (*Defn*)AtSymbol003==@[mode]
                             IN
                               [AtSymbol003 EXCEPT!.self[thisHost]=(@\intersect msg.value)]
                           ELSE
                             @[mode]
                         ]
                     ]
                 ]
               ELSE IF msg.fileField \in FilePathField
               THEN
                 [FileValueTableState EXCEPT![msg.fileField.fileID].path=msg.value]
               ELSE
                 UNCHANGED FileValueTableState

(*Defn*)ProcessInfiniteChildLeaseGrantMessage==
  \E sender \in Server,msg \in InfiniteChildLeaseGrantMessage:
     LET
       (*Defn*)fileSingletonFields==FileFieldToFileSingletonFieldSet(msg.fileField)
     IN
       /\ ReceiveMessage(sender,msg)
       /\ NoChangeToMessageLog
       /\ NoChangeToLeaseRecallMessageBuffer
       /\ SendNoMessage
       /\ IF \neg ServerOwnsFile(sender,msg.fileField.fileID)
          THEN
            /\ UNCHANGED ActiveProtectionRecords
            /\ UNCHANGED FileValueTableState
          ELSE IF
            /\ (\neg msg.extension)
            /\ ( \E rw \in PReadOrWrite,fileSingletonField \in fileSingletonFields:
                    HaveIndividualLeaseOnFileSingletonField(fileSingletonField,rw))
          THEN
            /\ UNCHANGED ActiveProtectionRecords
            /\ UNCHANGED FileValueTableState
          ELSE
            /\ UpdateProtectionRecordsWithLeaseGrant(
                 fileSingletonFields,msg.rw,PIndividual,msg.expiration)
            /\ IF msg.extension
               THEN
                 UNCHANGED FileValueTableState
               ELSE
                 (FileValueTableState')=
                 [FileValueTableState EXCEPT
                   ![msg.fileID].children=
                     [label \in Label|->
                       IF label \in msg.fileField.excludedLabels
                       THEN
                         @
                       ELSE
                         LET
                           (*Defn*)child==CHOOSE child \in msg.childValueSet:child.label=label
                         IN
                           IF
                             /\ child \in msg.childValueSet
                             /\ child.label=label
                           THEN
                             child.value
                           ELSE
                             Nil
                     ]
                 ]

(*Defn*)ProcessSingletonLeaseGrantCertificateMessage==
  \E sender \in Server,msg \in CertificateMessage:
     /\ ReceiveMessage(sender,msg)
     /\ NoChangeToMessageLog
     /\ NoChangeToLeaseRecallMessageBuffer
     /\ SendNoMessage
     /\ msg.cert \in SingletonLeaseGrantCertificates
     /\ IF
          \A server \in Server:
             ServerOwnsFile(server,msg.cert.fileID)=>
             ( \neg IsCertificateSignedBySignatory(msg.cert,server))
        THEN
          /\ UNCHANGED ActiveProtectionRecords
          /\ UNCHANGED FileValueTableState
        ELSE
          /\ UpdateProtectionRecordsWithLeaseGrant(
               {msg.cert.fileField},msg.cert.rw,PEveryone,msg.cert.expiration)
          /\ IF msg.cert.rw=PWrite
             THEN
               UNCHANGED FileValueTableState
             ELSE
               (FileValueTableState')=
               IF msg.cert.fileField \in FileSharedValueFields
               THEN
                 [FileValueTableState EXCEPT
                   ![msg.cert.fileField.fileID][msg.cert.fileField.field]=msg.cert.value
                 ]
               ELSE IF msg.cert.fileField \in FileChildField
               THEN
                 [FileValueTableState EXCEPT
                   ![msg.cert.fileField.fileID].children[msg.cert.fileField.label]=
                     msg.cert.value
                 ]
               ELSE IF msg.cert.fileField \in FilePathField
               THEN
                 [FileValueTableState EXCEPT![msg.cert.fileField.fileID].path=msg.cert.value]
               ELSE
                 UNCHANGED FileValueTableState

(* ********** Lease Extension, Release, and Recovery *********************************************************************** *)

(*Defn*)RequestLeaseExtension==
  \E fileSingletonField \in FileSingletonField,rw \in PReadOrWrite:
     /\ HaveIndividualLeaseOnFileSingletonField(fileSingletonField,rw)
     /\ ReceiveNoMessage
     /\ NoChangeToLeaseRecallMessageBuffer
     /\ UNCHANGED FileValueTableState
     /\ IF KnowFileCreationInProgress(fileSingletonField.fileID)
        THEN
          /\ LocallyExtendLease(fileSingletonField,rw)
          /\ SendNoMessage
        ELSE
          \E server \in Server:
             /\ ServerOwnsFile(server,fileSingletonField.fileID)
             /\ NoChangeToMessageLog
             /\ UNCHANGED ActiveProtectionRecords
             /\ SendMessage(server,MakeLeaseExtensionRequestMessage(fileSingletonField,rw))

(*Defn*)ProactivelyReleaseLease==
  \E oldProtectionRecord \in ActiveProtectionRecords:
     LET
       (*Defn*)newProtectionRecord==
         [oldProtectionRecord EXCEPT!.individual.endSerNum=ActionSerialNumber]
     IN
       /\ ( \/ oldProtectionRecord.fileField \notin FileOpenHandleField \union FileModeField
            \/ oldProtectionRecord.fileField.so#BBSelf
            \/ oldProtectionRecord.rw#PRead)
       /\ NowEarlierThan(oldProtectionRecord.individual.expiration)
       /\ oldProtectionRecord.individual.endSerNum=Infinity
       /\ ReceiveNoMessage
       /\ NoChangeToLeaseRecallMessageBuffer
       /\ SendNoMessage
       /\ UNCHANGED FileValueTableState
       /\ (ActiveProtectionRecords')=
          (ActiveProtectionRecords \ {oldProtectionRecord})\union{newProtectionRecord}
       /\ PostMessageInLog(
            MakeLeaseReleaseMessage(
              oldProtectionRecord.fileField,oldProtectionRecord.rw))

(*Defn*)RecoverOpenHandleReadSelfLease==
  \E fileID \in FileID:
     /\ (\neg HaveOpenHandleLease(fileID,BBSelf,PRead))
     /\ FileValueTableState[fileID].openHandle.self[thisHost]#{}
     /\ ReceiveNoMessage
     /\ NoChangeToLeaseRecallMessageBuffer
     /\ NoChangeToMessageLog
     /\ UNCHANGED ActiveProtectionRecords
     /\ UNCHANGED FileValueTableState
     /\ ( \E server \in Server:
             /\ ServerOwnsFile(server,fileID)
             /\ SendMessage(server,MakeOpenHandleReadSelfRequestMessage(fileID)))

(*Defn*)RecoverBonaFideLease==
  \E fileID \in FileID:
     /\ (\neg HaveBonaFideLease(fileID))
     /\ FileValueTableState[fileID].bonaFide[thisHost]#{}
     /\ ReceiveNoMessage
     /\ NoChangeToLeaseRecallMessageBuffer
     /\ NoChangeToMessageLog
     /\ UNCHANGED ActiveProtectionRecords
     /\ UNCHANGED FileValueTableState
     /\ ( \E server \in Server:
             /\ ServerOwnsFile(server,fileID)
             /\ SendMessage(server,MakeBonaFideRequestMessage(fileID)))
====
