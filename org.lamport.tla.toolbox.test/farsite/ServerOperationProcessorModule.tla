---- MODULE ServerOperationProcessorModule ----
(*`^\addcontentsline{toc}{section}{ServerOperationProcessorModule}^'*)

EXTENDS
  ServerKnowledgePredicatesModule,
  ServerReviewPredicatesModule,
  ServerMessageBuffersModule
(* ********** Single-Server Operations ************************************************************************************* *)

(*Defn*)ProcessOpenFileOperation==
  \E msg \in OpenFileOperationMessage,client \in Client:
     /\ DequeueClientConsistencyMessage(msg,client)
     /\ NoChangeToInterlockMessageBuffer
     /\ UNCHANGED FileProtectionTableState
     /\ NoChangeToFileOwnership
     /\ IF
          /\ ClientKnewModeSetCompatible(client,msg.fileID,msg.modes)
          /\ ClientKnewFileNotDeletePending(client,msg.fileID)
          /\ IF msg.firstHandle
             THEN
               /\ ClientKnewNoHandleOpenOnFile(client,msg.fileID)
               /\ ClientKnewCouldOpenOrCloseFile(client,msg.fileID)
             ELSE
               ClientKnewSomeHandleOpenOnFile(client,msg.fileID)
          /\ ClientHasBonaFideLease(client,msg.fileID)
          /\ ( \A mode \in msg.modes:
                  IF mode \in msg.firstModes
                  THEN
                    /\ ClientKnewNoHandleHadModeOnFile(client,mode,msg.fileID)
                    /\ ClientKnewCouldSetOrClearFileMode(client,msg.fileID,mode)
                  ELSE
                    ClientKnewSomeHandleHadModeOnFile(client,mode,msg.fileID))
        THEN
          /\ (FileValueTableState')=
             [
               [
                 [
                   [FileValueTableState EXCEPT
                     ![msg.fileID].openHandle.self[client]=(@\union{msg.handle})
                   ]
                 EXCEPT
                   ![msg.fileID].bonaFide[client]=(@\union{msg.handle})
                 ]
               EXCEPT
                 ![msg.fileID]=
                   [@EXCEPT
                     !.modes=
                       [mode \in DOMAIN@|->
                         IF mode \in msg.modes
                         THEN
                           LET
                             (*Defn*)AtSymbol001==@[mode]
                           IN
                             [AtSymbol001 EXCEPT!.self[client]=(@\union{msg.handle})]
                         ELSE
                           @[mode]
                       ]
                   ]
               ]
             EXCEPT
               ![msg.fileID]=
                 [@EXCEPT
                   !.accesses=
                     [access \in DOMAIN@|->
                       IF access \in ModeSetToAccessSet(msg.modes)
                       THEN
                         LET
                           (*Defn*)AtSymbol002==@[access]
                         IN
                           [AtSymbol002 EXCEPT!.self[client]=(@\union{msg.handle})]
                       ELSE
                         @[access]
                     ]
                 ]
             ]
          /\ SendMessage(client,MakePositiveAcknowledgementMessage(msg.ackID))
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ SendNoMessage

(*Defn*)ProcessCleanupFileOperation==
  \E msg \in CleanupFileOperationMessage,client \in Client:
     /\ DequeueClientConsistencyMessage(msg,client)
     /\ NoChangeToInterlockMessageBuffer
     /\ UNCHANGED FileProtectionTableState
     /\ NoChangeToFileOwnership
     /\ IF
          /\ msg.handle \notin RootHandle
          /\ ClientKnewHandleOpenOnFile(client,msg.handle,msg.fileID)
          /\ ClientKnewHandleOnFileWasBonaFide(client,msg.handle,msg.fileID)
          /\ ( \A mode \in Mode:
                  IF mode \in msg.modes
                  THEN
                    /\ ClientKnewHandleHadModeOnFile(client,msg.handle,mode,msg.fileID)
                    /\ IF mode \in msg.lastModes
                       THEN
                         /\ ClientKnewNoOtherHandleHadModeOnFile(client,msg.handle,mode,msg.fileID)
                         /\ ClientKnewCouldSetOrClearFileMode(client,msg.fileID,mode)
                       ELSE
                         ClientKnewAnotherHandleHadModeOnFile(client,msg.handle,mode,msg.fileID)
                  ELSE
                    ClientKnewHandleLackedModeOnFile(client,msg.handle,mode,msg.fileID))
        THEN
          /\ (FileValueTableState')=
             [
               [FileValueTableState EXCEPT![msg.fileID].bonaFide[client]=(@\ {msg.handle})]
             EXCEPT
               ![msg.fileID]=
                 [@EXCEPT
                   !.modes=
                     [mode \in DOMAIN@|->
                       IF mode \in Mode
                       THEN
                         LET
                           (*Defn*)AtSymbol003==@[mode]
                         IN
                           [AtSymbol003 EXCEPT!.self[client]=(@\ {msg.handle})]
                       ELSE
                         @[mode]
                     ]
                 ]
             ]
          /\ SendMessage(client,MakePositiveAcknowledgementMessage(msg.ackID))
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ SendNoMessage

(*Defn*)ProcessCloseFileOperation==
  \E msg \in CloseFileOperationMessage,client \in Client:
     /\ DequeueClientConsistencyMessage(msg,client)
     /\ NoChangeToInterlockMessageBuffer
     /\ UNCHANGED FileProtectionTableState
     /\ NoChangeToFileOwnership
     /\ IF
          /\ msg.handle \notin RootHandle
          /\ ClientKnewHandleOpenOnFile(client,msg.handle,msg.fileID)
          /\ ClientKnewHandleOnFileNotBonaFide(client,msg.handle,msg.fileID)
          /\ IF msg.unlinkPreclusion=UPNotLastHandle
             THEN
               ClientKnewAnotherHandleOpenOnFile(client,msg.handle,msg.fileID)
             ELSE
               /\ ClientKnewNoOtherHandleOpenOnFile(client,msg.handle,msg.fileID)
               /\ ClientKnewCouldOpenOrCloseFile(client,msg.fileID)
               /\ IF msg.unlinkPreclusion=UPDelDispFalse
                  THEN
                    ClientKnewFileNotDeletePending(client,msg.fileID)
                  ELSE
                    ClientKnewFileOpenedByAnotherClient(client,msg.fileID)
        THEN
          /\ (FileValueTableState')=
             [
               [FileValueTableState EXCEPT
                 ![msg.fileID].openHandle.self[client]=(@\ {msg.handle})
               ]
             EXCEPT
               ![msg.fileID]=
                 [@EXCEPT
                   !.accesses=
                     [access \in DOMAIN@|->
                       IF access \in Access
                       THEN
                         LET
                           (*Defn*)AtSymbol004==@[access]
                         IN
                           [AtSymbol004 EXCEPT![client]=(@\ {msg.handle})]
                       ELSE
                         @[access]
                     ]
                 ]
             ]
          /\ SendMessage(client,MakePositiveAcknowledgementMessage(msg.ackID))
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ SendNoMessage

(*Defn*)ProcessWriteFileOperation==
  \E msg \in WriteFileOperationMessage,client \in Client:
     /\ DequeueClientConsistencyMessage(msg,client)
     /\ NoChangeToInterlockMessageBuffer
     /\ UNCHANGED FileProtectionTableState
     /\ NoChangeToFileOwnership
     /\ IF
          /\ ClientKnewHandleOpenOnFile(client,msg.handle,msg.fileID)
          /\ ClientKnewHandleHadAccessToFile(client,msg.handle,ATWritable,msg.fileID)
          /\ ClientHasWriteSVLease(client,msg.fileID,FContent)
        THEN
          /\ (FileValueTableState')=
             [FileValueTableState EXCEPT![msg.fileID].content=msg.content]
          /\ SendMessage(client,MakePositiveAcknowledgementMessage(msg.ackID))
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ SendNoMessage

(*Defn*)ProcessCreateFileOperation==
  \E msg \in CreateFileOperationMessage,client \in Client:
     /\ DequeueClientConsistencyMessage(msg,client)
     /\ NoChangeToInterlockMessageBuffer
     /\ UNCHANGED OwnershipAuthorizingServer
     /\ UNCHANGED IssuedDeeds
     /\ NoChangeToFileMap
     /\ IF
          /\ ClientKnewLabelWasUnused(client,msg.parentFile,msg.label)
          /\ ClientKnewFileNotDeletePending(client,msg.parentFile)
          /\ ClientHasWriteChildLease(client,msg.parentFile,msg.label)
          /\ msg.parentFile=AllButLast(msg.fileID)
          /\ FileHasBeenBorrowedByClient(msg.fileID,client)
          /\ msg.sharedValueLeaseTime \leq LateClock+ClientShortLeaseTimeLimit
          /\ msg.blackBoxReadSelfLeaseTime \leq LateClock+ClientLongLeaseTimeLimit
          /\ msg.blackBoxWriteSelfLeaseTime \leq LateClock+ClientShortLeaseTimeLimit
          /\ msg.blackBoxReadOtherLeaseTime \leq LateClock+ClientShortLeaseTimeLimit
          /\ msg.privateValueLeaseTime \leq LateClock+ClientLongLeaseTimeLimit
        THEN
          /\ (FileValueTableState')=
             [FileValueTableState EXCEPT
               ![msg.parentFile].children[msg.label]=msg.fileID,
               ![msg.fileID]=
                 [
                   [
                     [
                       [[FileValueInit EXCEPT!.parent=MakeParent(msg.parentFile,msg.label)]EXCEPT
                         !.openHandle.self[client]={msg.handle}
                       ]
                     EXCEPT
                       !.bonaFide[client]={msg.handle}
                     ]
                   EXCEPT
                     !.modes=
                       [mode \in DOMAIN@|->
                         IF mode \in msg.modes
                         THEN
                           LET
                             (*Defn*)AtSymbol005==@[mode]
                           IN
                             [AtSymbol005 EXCEPT!.self[client]={msg.handle}]
                         ELSE
                           @[mode]
                       ]
                   ]
                 EXCEPT
                   !.accesses=
                     [access \in DOMAIN@|->
                       IF access \in ModeSetToAccessSet(msg.modes)
                       THEN
                         LET(*Defn*)AtSymbol006==@[access]IN[AtSymbol006 EXCEPT![client]={msg.handle}]
                       ELSE
                         @[access]
                     ]
                 ]
             ]
          /\ (FileProtectionTableState')=
             [
               [
                 [
                   [
                     [
                       [
                         [
                           [FileProtectionTableState EXCEPT
                             ![msg.fileID]=
                               [field \in DOMAIN@|->
                                 IF field \in FSharedValueFields
                                 THEN
                                   LET
                                     (*Defn*)AtSymbol007==@[field]
                                   IN
                                     [AtSymbol007 EXCEPT!.individual[client].write=msg.sharedValueLeaseTime]
                                 ELSE
                                   @[field]
                               ]
                           ]
                         EXCEPT
                           ![msg.fileID].children.infinite=
                             InfiniteChild({},client,msg.sharedValueLeaseTime)
                         ]
                       EXCEPT
                         ![msg.fileID].openHandle.self.individual[client].read=
                           msg.blackBoxReadSelfLeaseTime
                       ]
                     EXCEPT
                       ![msg.fileID].openHandle.self.individual[client].write=
                         msg.blackBoxWriteSelfLeaseTime
                     ]
                   EXCEPT
                     ![msg.fileID].openHandle.other.individual[client].read=
                       msg.blackBoxReadOtherLeaseTime
                   ]
                 EXCEPT
                   ![msg.fileID].bonaFide.individual[client].read=msg.privateValueLeaseTime
                 ]
               EXCEPT
                 ![msg.fileID]=
                   [@EXCEPT
                     !.modes=
                       [mode \in DOMAIN@|->
                         IF mode \in Mode
                         THEN
                           LET
                             (*Defn*)AtSymbol008==@[mode]
                           IN
                             [AtSymbol008 EXCEPT
                               !.self.individual[client].write=msg.blackBoxWriteSelfLeaseTime
                             ]
                         ELSE
                           @[mode]
                       ]
                   ]
               ]
             EXCEPT
               ![msg.fileID]=
                 [@EXCEPT
                   !.modes=
                     [mode \in DOMAIN@|->
                       IF mode \in Mode
                       THEN
                         LET
                           (*Defn*)AtSymbol009==@[mode]
                         IN
                           [AtSymbol009 EXCEPT
                             !.other.individual[client].read=msg.blackBoxReadOtherLeaseTime
                           ]
                       ELSE
                         @[mode]
                     ]
                 ]
             ]
          /\ AcceptReturnedFileAndLendIchildren(msg.fileID,msg.borrowedMaxSuffix)
          /\ SendMessage(client,MakePositiveAcknowledgementMessage(msg.ackID))
        ELSE
          /\ UNCHANGED FileProtectionTableState
          /\ UNCHANGED ActiveBorrowerRecords
          /\ UNCHANGED FileValueTableState
          /\ SendNoMessage

(*Defn*)ProcessDeleteFileOperation==
  \E msg \in DeleteFileOperationMessage,client \in Client:
     /\ DequeueClientConsistencyMessage(msg,client)
     /\ NoChangeToInterlockMessageBuffer
     /\ UNCHANGED FileProtectionTableState
     /\ NoChangeToFileOwnership
     /\ IF
          /\ ClientKnewHandleOpenOnFile(client,msg.handle,msg.fileID)
          /\ ClientKnewHandleOnFileWasBonaFide(client,msg.handle,msg.fileID)
          /\ ClientKnewHandleHadModeOnFile(client,msg.handle,MTAccessDelete,msg.fileID)
          /\ (msg.delDisp=>ClientKnewFileHadNoChildren(client,msg.fileID))
          /\ ClientHasWriteSVLease(client,msg.fileID,FDelDisp)
        THEN
          /\ (FileValueTableState')=
             [FileValueTableState EXCEPT![msg.fileID].delDisp=msg.delDisp]
          /\ SendMessage(client,MakePositiveAcknowledgementMessage(msg.ackID))
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ SendNoMessage

(* ********** Multi-Server Operation: CloseAndUnlink *********************************************************************** *)

(*Defn*)ChildPrepareCloseAndUnlinkFileOperation==
  \E opMsg \in CloseAndUnlinkFileOperationMessage,client \in Client:
     /\ MessageInClientConsistencyBuffer(opMsg,client)
     /\ opMsg.destinationField=CAUDChildFile
     /\ FileProtectionTableState[opMsg.childFile].parent.reservation=
        Reservation(Nil,Nil,MakeParent(Nil,Nil))
     /\ NoChangeToInterlockMessageBuffer
     /\ UNCHANGED FileValueTableState
     /\ IF
          /\ ClientKnewHandleOpenOnFile(client,opMsg.handle,opMsg.childFile)
          /\ ClientKnewHandleOnFileNotBonaFide(client,opMsg.handle,opMsg.childFile)
          /\ ClientKnewNoOtherHandleOpenOnFile(client,opMsg.handle,opMsg.childFile)
          /\ ClientKnewFileNotOpenedByAnotherClient(client,opMsg.childFile)
          /\ ClientKnewFileDeletePending(client,opMsg.childFile)
          /\ ClientKnewCouldOpenOrCloseFile(client,opMsg.childFile)
          /\ ClientHasOpenHandleLease(client,opMsg.childFile,BBOther,PRead)
          /\ ClientHasBonaFideLease(client,opMsg.childFile)
          /\ (\A mode \in Mode:ClientHasModeLease(client,opMsg.childFile,mode,BBSelf))
          /\ (\A mode \in Mode:ClientHasModeLease(client,opMsg.childFile,mode,BBOther))
          /\ ( \A field \in FSharedValueFields:
                  ClientHasWriteSVLease(client,opMsg.childFile,field))
          /\ (\A label \in Label:ClientHasWriteChildLease(client,opMsg.childFile,label))
          /\ ClientKnewParentFile(client,opMsg.childFile,opMsg.label,opMsg.parentFile)
        THEN
          /\ NoChangeToConsistencyMessageBuffer
          /\ (FileProtectionTableState')=
             [FileProtectionTableState EXCEPT
               ![opMsg.childFile].parent.reservation=
                 Reservation(client,opMsg.parentFile,MakeParent(Nil,Nil))
             ]
          /\ ( \E parentServer \in Server,deadlineTime \in ServerInterlockTimeRange:
                  /\ ServerOwnsFile(parentServer,opMsg.parentFile)
                  /\ SendMessage(
                       parentServer,
                       MakeParentFieldReservedMessage(
                         opMsg.parentFile,
                         opMsg.childFile,
                         MakeParent(Nil,Nil),
                         client,
                         LateClock+deadlineTime)))
        ELSE
          /\ UNCHANGED FileProtectionTableState
          /\ DequeueClientConsistencyMessage(opMsg,client)
          /\ SendNoMessage

(*Defn*)ChildCommitCloseAndUnlinkFileOperation==
  \E upfMsg \in UpdateParentFieldMessage:
     /\ WithdrawServerInterlockMessageSet({upfMsg})
     /\ upfMsg.newLabel=Nil
     /\ upfMsg.newFile=Nil
     /\ IF
          FileProtectionTableState[upfMsg.destFile].parent.reservation=
          Reservation(upfMsg.initiator,upfMsg.srcFile,MakeParent(Nil,Nil))
        THEN
          /\ (FileValueTableState')=
             [FileValueTableState EXCEPT![upfMsg.destFile]=FileValueInit]
          /\ (FileProtectionTableState')=
             [FileProtectionTableState EXCEPT
               ![upfMsg.destFile]=
                 [FileProtectionInit EXCEPT
                   !.maxSuffix=FileProtectionTableState[upfMsg.destFile].maxSuffix
                 ]
             ]
          /\ IF
               \A opMsg \in CloseAndUnlinkFileOperationMessage:
                  MessageInClientConsistencyBuffer(opMsg,upfMsg.initiator)=>
                  \/ opMsg.destinationField#CAUDChildFile
                  \/ opMsg.childFile#upfMsg.destFile
                  \/ opMsg.parentFile#upfMsg.srcFile
             THEN
               /\ NoChangeToConsistencyMessageBuffer
               /\ SendNoMessage
             ELSE
               \E opMsg \in CloseAndUnlinkFileOperationMessage:
                  /\ DequeueClientConsistencyMessage(opMsg,upfMsg.initiator)
                  /\ opMsg.destinationField=CAUDChildFile
                  /\ opMsg.childFile=upfMsg.destFile
                  /\ opMsg.parentFile=upfMsg.srcFile
                  /\ SendMessage(upfMsg.initiator,MakePositiveAcknowledgementMessage(opMsg.ackID))
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ NoChangeToConsistencyMessageBuffer
          /\ SendNoMessage

(*Defn*)ChildAbortCloseAndUnlinkFileOperation==
  \E upfMsg \in UnreserveParentFieldMessage:
     /\ WithdrawServerInterlockMessageSet({upfMsg})
     /\ FileProtectionTableState[upfMsg.destFile].parent.reservation.value.fileID=Nil
     /\ SendNoMessage
     /\ UNCHANGED FileValueTableState
     /\ IF
          FileProtectionTableState[upfMsg.destFile].parent.reservation.leader=
          upfMsg.srcFile
        THEN
          /\ (FileProtectionTableState')=
             [FileProtectionTableState EXCEPT
               ![upfMsg.destFile].parent.reservation=
                 Reservation(Nil,Nil,MakeParent(Nil,Nil))
             ]
          /\ IF
               \A opMsg \in MoveFileOperationMessage:
                  MessageInClientConsistencyBuffer(opMsg,upfMsg.initiator)=>
                  \/ opMsg.destinationField#CAUDChildFile
                  \/ opMsg.childFile#upfMsg.destFile
                  \/ opMsg.parentFile#upfMsg.srcFile
             THEN
               NoChangeToConsistencyMessageBuffer
             ELSE
               \E opMsg \in CloseAndUnlinkFileOperationMessage:
                  /\ opMsg.destinationField=CAUDChildFile
                  /\ opMsg.childFile=upfMsg.destFile
                  /\ opMsg.parentFile=upfMsg.srcFile
                  /\ ExpireClientConsistencyMessage(opMsg,upfMsg.initiator)
        ELSE
          /\ UNCHANGED FileProtectionTableState
          /\ NoChangeToConsistencyMessageBuffer

(*Defn*)ParentProcessCloseAndUnlinkFileOperation==
  \E opMsg \in CloseAndUnlinkFileOperationMessage,
     pfrMsg \in ParentFieldReservedMessage,
     client \in Client,
     childServer \in Server
     :
     /\ opMsg.destinationField=CAUDParentFile
     /\ DequeueClientConsistencyMessage(opMsg,client)
     /\ WithdrawServerInterlockMessageSet({pfrMsg})
     /\ pfrMsg.destFile=opMsg.parentFile
     /\ pfrMsg.srcFile=opMsg.childFile
     /\ pfrMsg.reservation=MakeParent(Nil,Nil)
     /\ pfrMsg.initiator=client
     /\ ServerOwnsFile(childServer,opMsg.childFile)
     /\ UNCHANGED FileProtectionTableState
     /\ IF
          /\ ClientKnewChildFile(client,opMsg.parentFile,opMsg.label,opMsg.childFile)
          /\ ClientHasWriteChildLease(client,opMsg.parentFile,opMsg.label)
        THEN
          /\ (FileValueTableState')=
             [FileValueTableState EXCEPT![opMsg.parentFile].children[opMsg.label]=Nil]
          /\ SendAddressedMessageSet(
               {
               MakeAddressedMessage(
                 childServer,
                 MakeUpdateParentFieldMessage(
                   opMsg.childFile,opMsg.parentFile,Nil,Nil,client)),
               MakeAddressedMessage(client,MakePositiveAcknowledgementMessage(opMsg.ackID))
               })
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ SendMessage(
               childServer,
               MakeUnreserveParentFieldMessage(opMsg.childFile,opMsg.parentFile))

(*Defn*)ProcessCloseAndUnlinkFileOperation==
  /\ NoChangeToFileOwnership
  /\ ( \/ ChildPrepareCloseAndUnlinkFileOperation
       \/ ChildCommitCloseAndUnlinkFileOperation
       \/ ChildAbortCloseAndUnlinkFileOperation
       \/ ParentProcessCloseAndUnlinkFileOperation)

(* ********** Multi-Server Operation: Move ********************************************************************************* *)

(*Defn*)ChildPrepareMoveFileOperation==
  \E opMsg \in MoveFileOperationMessage,client \in Client:
     /\ MessageInClientConsistencyBuffer(opMsg,client)
     /\ opMsg.destinationField=MDChildFile
     /\ FileProtectionTableState[opMsg.childFile].parent.reservation=
        Reservation(Nil,Nil,MakeParent(Nil,Nil))
     /\ NoChangeToInterlockMessageBuffer
     /\ UNCHANGED FileValueTableState
     /\ IF
          /\ ClientKnewHandleOpenOnFile(client,opMsg.childHandle,opMsg.childFile)
          /\ ClientKnewHandleOnFileWasBonaFide(client,opMsg.childHandle,opMsg.childFile)
          /\ ClientHasWriteSVLease(client,opMsg.childFile,FParent)
          /\ ClientKnewParentFile(
               client,opMsg.childFile,opMsg.srcLabel,opMsg.srcParentFile)
        THEN
          /\ NoChangeToConsistencyMessageBuffer
          /\ (FileProtectionTableState')=
             [FileProtectionTableState EXCEPT
               ![opMsg.childFile].parent.reservation=
                 Reservation(
                   client,opMsg.srcParentFile,MakeParent(opMsg.destParentFile,opMsg.destLabel))
             ]
          /\ ( \E srcParentServer \in Server,
                  destParentServer \in Server,
                  deadlineTime \in ServerInterlockTimeRange
                  :
                  /\ ServerOwnsFile(srcParentServer,opMsg.srcParentFile)
                  /\ ServerOwnsFile(destParentServer,opMsg.destParentFile)
                  /\ SendAddressedMessageSet(
                       {
                       MakeAddressedMessage(
                         srcParentServer,
                         MakeParentFieldReservedMessage(
                           opMsg.srcParentFile,
                           opMsg.childFile,
                           MakeParent(opMsg.destParentFile,opMsg.destLabel),
                           client,
                           LateClock+deadlineTime)),
                       MakeAddressedMessage(
                         destParentServer,
                         MakeParentFieldReservedIndicationMessage(
                           opMsg.destParentFile,
                           opMsg.childFile,
                           MakeParent(opMsg.destParentFile,opMsg.destLabel),
                           client))
                       }))
        ELSE
          /\ DequeueClientConsistencyMessage(opMsg,client)
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage

(*Defn*)ChildCommitMoveFileOperation==
  \E upfMsg \in UpdateParentFieldMessage:
     /\ WithdrawServerInterlockMessageSet({upfMsg})
     /\ upfMsg.label \in Label
     /\ upfMsg.newFile \in FileID
     /\ IF
          FileProtectionTableState[upfMsg.destFile].parent.reservation=
          Reservation(
            upfMsg.initiator,upfMsg.srcFile,MakeParent(upfMsg.newFile,upfMsg.label))
        THEN
          /\ (FileValueTableState')=
             [FileValueTableState EXCEPT
               ![upfMsg.destFile].parent=MakeParent(upfMsg.newFile,upfMsg.label)
             ]
          /\ (FileProtectionTableState')=
             [FileProtectionTableState EXCEPT
               ![upfMsg.destFile].parent.reservation=
                 Reservation(Nil,Nil,MakeParent(Nil,Nil))
             ]
          /\ IF
               \A opMsg \in MoveFileOperationMessage:
                  MessageInClientConsistencyBuffer(opMsg,upfMsg.initiator)=>
                  \/ opMsg.destinationField#MDChildFile
                  \/ opMsg.childFile#upfMsg.destFile
                  \/ opMsg.srcParentFile#upfMsg.srcFile
                  \/ opMsg.destParentFile#upfMsg.newFile
                  \/ opMsg.destLabel#upfMsg.label
             THEN
               /\ NoChangeToConsistencyMessageBuffer
               /\ ( \E destParentServer \in Server:
                       /\ ServerOwnsFile(destParentServer,upfMsg.newFile)
                       /\ SendMessage(
                            destParentServer,
                            MakeParentFieldUpdatedMessage(
                              upfMsg.newFile,upfMsg.destFile,upfMsg.label,upfMsg.newFile)))
             ELSE
               \E opMsg \in MoveFileOperationMessage,destParentServer \in Server:
                  /\ DequeueClientConsistencyMessage(opMsg,upfMsg.initiator)
                  /\ opMsg.destinationField=MDChildFile
                  /\ opMsg.childFile=upfMsg.destFile
                  /\ opMsg.srcParentFile=upfMsg.srcFile
                  /\ opMsg.destParentFile=upfMsg.newFile
                  /\ opMsg.destLabel=upfMsg.label
                  /\ ServerOwnsFile(destParentServer,upfMsg.newFile)
                  /\ SendAddressedMessageSet(
                       {
                       MakeAddressedMessage(
                         upfMsg.initiator,MakePositiveAcknowledgementMessage(opMsg.ackID)),
                       MakeAddressedMessage(
                         destParentServer,
                         MakeParentFieldUpdatedMessage(
                           upfMsg.newFile,upfMsg.destFile,upfMsg.label,upfMsg.newFile))
                       })
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ NoChangeToConsistencyMessageBuffer
          /\ SendNoMessage

(*Defn*)ChildAbortMoveFileOperation==
  \E upfMsg \in UnreserveParentFieldMessage:
     LET
       (*Defn*)destParentFile==
         FileProtectionTableState[upfMsg.destFile].parent.reservation.value.fileID
     IN
       /\ WithdrawServerInterlockMessageSet({upfMsg})
       /\ destParentFile \in FileID
       /\ UNCHANGED FileValueTableState
       /\ IF
            FileProtectionTableState[upfMsg.destFile].parent.reservation.leader=
            upfMsg.srcFile
          THEN
            /\ (FileProtectionTableState')=
               [FileProtectionTableState EXCEPT
                 ![upfMsg.destFile].parent.reservation=
                   Reservation(Nil,Nil,MakeParent(Nil,Nil))
               ]
            /\ ( \E destParentServer \in Server:
                    /\ ServerOwnsFile(destParentServer,destParentFile)
                    /\ SendMessage(
                         destParentServer,
                         MakeParentFieldUnreservedMessage(destParentFile,upfMsg.destFile))
                    /\ IF
                         \A opMsg \in MoveFileOperationMessage:
                            MessageInClientConsistencyBuffer(opMsg,upfMsg.initiator)=>
                            \/ opMsg.destinationField#MDChildFile
                            \/ opMsg.childFile#upfMsg.destFile
                            \/ opMsg.srcParentFile#upfMsg.srcFile
                       THEN
                         NoChangeToConsistencyMessageBuffer
                       ELSE
                         \E opMsg \in MoveFileOperationMessage:
                            /\ opMsg.destinationField=MDChildFile
                            /\ opMsg.childFile=upfMsg.destFile
                            /\ opMsg.srcParentFile=upfMsg.srcFile
                            /\ ExpireClientConsistencyMessage(opMsg,upfMsg.initiator))
          ELSE
            /\ UNCHANGED FileProtectionTableState
            /\ NoChangeToConsistencyMessageBuffer
            /\ SendNoMessage

(*Defn*)DestinationPrepareMoveFileOperation==
  \E pfrMsg \in ParentFieldReservedMessage,
     opMsg \in MoveFileOperationMessage,
     client \in Client
     :
     /\ MessageInServerInterlockBuffer(pfrMsg)
     /\ MessageInClientConsistencyBuffer(opMsg,client)
     /\ opMsg.destinationField=MDDestParentFile
     /\ pfrMsg.srcFile=opMsg.childFile
     /\ pfrMsg.reservation=MakeParent(opMsg.destParentFile,opMsg.destLabel)
     /\ pfrMsg.initiator=client
     /\ FileProtectionTableState[opMsg.destParentFile].children.singleton
        [
        opMsg.destLabel
        ]
        .
        reservation
        =
        Reservation(Nil,Nil,Nil)
     /\ NoChangeToInterlockMessageBuffer
     /\ UNCHANGED FileValueTableState
     /\ IF
          /\ opMsg.childFile#opMsg.destParentFile
          /\ ( \E destAncestorPath \in FileSeq:
                  /\ ClientKnewFileHadWarrantiedAncestorPath(
                       client,opMsg.destParentFile,destAncestorPath)
                  /\ (\neg IsElementInSeq(opMsg.childFile,destAncestorPath)))
          /\ ClientKnewLabelWasUnused(client,opMsg.destParentFile,opMsg.destLabel)
          /\ ClientKnewFileNotDeletePending(client,opMsg.destParentFile)
          /\ ClientHasWriteChildLease(client,opMsg.destParentFile,opMsg.destLabel)
        THEN
          /\ NoChangeToConsistencyMessageBuffer
          /\ (FileProtectionTableState')=
             [FileProtectionTableState EXCEPT
               ![opMsg.destParentFile].children.singleton[opMsg.destLabel].reservation=
                 Reservation(client,opMsg.srcParentFile,opMsg.childFile)
             ]
          /\ ( \E srcParentServer \in Server,deadlineTime \in ServerInterlockTimeRange:
                  /\ ServerOwnsFile(srcParentServer,opMsg.srcParentFile)
                  /\ SendMessage(
                       srcParentServer,
                       MakeChildFieldReservedMessage(
                         opMsg.srcParentFile,
                         opMsg.destParentFile,
                         opMsg.destLabel,
                         opMsg.childFile,
                         client,
                         LateClock+deadlineTime)))
        ELSE
          /\ DequeueClientConsistencyMessage(opMsg,client)
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage

(*Defn*)DestinationCommitMoveFileOperation==
  \E ucfMsg \in UpdateChildFieldMessage:
     /\ MessageInServerInterlockBuffer(ucfMsg)
     /\ IF
          FileProtectionTableState[ucfMsg.destFile].children.singleton[ucfMsg.label]
          .
          reservation
          =
          Reservation(ucfMsg.initiator,ucfMsg.srcFile,ucfMsg.newFile)
        THEN
          \E pfrMsg \in ParentFieldReservedMessage,pfuMsg \in ParentFieldUpdatedMessage:
             /\ WithdrawServerInterlockMessageSet({ucfMsg,pfrMsg,pfuMsg})
             /\ pfrMsg.destFile=ucfMsg.destFile
             /\ pfrMsg.srcFile=ucfMsg.newFile
             /\ pfrMsg.reservation=MakeParent(ucfMsg.destFile,ucfMsg.label)
             /\ pfrMsg.initiator=ucfMsg.initiator
             /\ pfuMsg.destFile=ucfMsg.destFile
             /\ pfuMsg.srcFile=ucfMsg.newFile
             /\ pfuMsg.newLabel=ucfMsg.label
             /\ pfuMsg.newFile=ucfMsg.destFile
             /\ (FileValueTableState')=
                [FileValueTableState EXCEPT
                  ![ucfMsg.destFile].children[ucfMsg.label]=ucfMsg.newFile
                ]
             /\ (FileProtectionTableState')=
                [FileProtectionTableState EXCEPT
                  ![ucfMsg.destFile].children.singleton[ucfMsg.label].reservation=
                    Reservation(Nil,Nil,Nil)
                ]
             /\ IF
                  \A opMsg \in MoveFileOperationMessage:
                     MessageInClientConsistencyBuffer(opMsg,ucfMsg.initiator)=>
                     \/ opMsg.destinationField#MDDestParentFile
                     \/ opMsg.childFile#ucfMsg.newFile
                     \/ opMsg.srcParentFile#ucfMsg.srcFile
                     \/ opMsg.destParentFile#ucfMsg.destFile
                     \/ opMsg.destLabel#ucfMsg.label
                THEN
                  /\ NoChangeToConsistencyMessageBuffer
                  /\ SendNoMessage
                ELSE
                  \E opMsg \in MoveFileOperationMessage:
                     /\ DequeueClientConsistencyMessage(opMsg,ucfMsg.initiator)
                     /\ opMsg.destinationField=MDDestParentFile
                     /\ opMsg.childFile=ucfMsg.newFile
                     /\ opMsg.srcParentFile=ucfMsg.srcFile
                     /\ opMsg.destParentFile=ucfMsg.destFile
                     /\ opMsg.destLabel=ucfMsg.label
                     /\ SendMessage(ucfMsg.initiator,MakePositiveAcknowledgementMessage(opMsg.ackID))
        ELSE
          /\ WithdrawServerInterlockMessageSet({ucfMsg})
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ NoChangeToConsistencyMessageBuffer
          /\ SendNoMessage

(*Defn*)DestinationAbortMoveFileOperation==
  \E ucfMsg \in UnreserveChildFieldMessage:
     /\ WithdrawServerInterlockMessageSet({ucfMsg})
     /\ SendNoMessage
     /\ UNCHANGED FileValueTableState
     /\ IF
          FileProtectionTableState[ucfMsg.destFile].children.singleton[ucfMsg.label]
          .
          reservation
          .
          leader
          =
          ucfMsg.srcFile
        THEN
          /\ (FileProtectionTableState')=
             [FileProtectionTableState EXCEPT
               ![ucfMsg.destFile].children.singleton[ucfMsg.label].reservation=
                 Reservation(Nil,Nil,Nil)
             ]
          /\ IF
               \A opMsg \in MoveFileOperationMessage:
                  MessageInClientConsistencyBuffer(opMsg,ucfMsg.initiator)=>
                  \/ opMsg.destinationField#MDDestParentFile
                  \/ opMsg.srcParentFile#ucfMsg.srcFile
                  \/ opMsg.destParentFile#ucfMsg.destFile
             THEN
               NoChangeToConsistencyMessageBuffer
             ELSE
               \E opMsg \in MoveFileOperationMessage:
                  /\ opMsg.destinationField=MDDestParentFile
                  /\ opMsg.srcParentFile=ucfMsg.srcFile
                  /\ opMsg.destParentFile=ucfMsg.destFile
                  /\ ExpireClientConsistencyMessage(opMsg,ucfMsg.initiator)
        ELSE
          /\ UNCHANGED FileProtectionTableState
          /\ NoChangeToConsistencyMessageBuffer

(*Defn*)DestinationCleanupMoveFileOperation==
  \E pfuMsg \in ParentFieldUnreservedMessage:
     /\ MessageInServerInterlockBuffer(pfuMsg)
     /\ UNCHANGED FileValueTableState
     /\ UNCHANGED FileProtectionTableState
     /\ SendNoMessage
     /\ NoChangeToConsistencyMessageBuffer
     /\ IF
          \A pfrMsg \in ParentFieldReservedMessage:
             MessageInServerInterlockBuffer(pfrMsg)=>
             \/ pfrMsg.srcFile#pfuMsg.srcFile
             \/ pfrMsg.destFile#pfuMsg.destFile
        THEN
          WithdrawServerInterlockMessageSet({pfuMsg})
        ELSE
          \E pfrMsg \in ParentFieldReservedMessage:
             /\ MessageInServerInterlockBuffer(pfrMsg)
             /\ pfrMsg.srcFile=pfuMsg.srcFile
             /\ pfrMsg.destFile=pfuMsg.destFile
             /\ WithdrawServerInterlockMessageSet({pfuMsg,pfrMsg})

(* This is an annoying little action.  It doesn't fit the standard pattern at all.
	Most spurious interlock messages are dealt with in the action that handles
	reasonable interlock messages, but there was no easy way to do this for this
	particular message.  The problem stems from the fact that the destination
	needs two interlock messages before it is willing to do its prepare.
	We don't really need this operation; we could allow detritus to accumulate in
	the InterlockMessageBuffer, but it seems like a good idea to include it. *)

(*Defn*)DestinationDiscardSpuriousParentFieldUpdatedMessage==
  \E pfuMsg \in ParentFieldUpdatedMessage:
     /\ WithdrawServerInterlockMessageSet({pfuMsg})
     /\ ( \A pfrMsg \in ParentFieldReservedMessage:
             MessageInServerInterlockBuffer(pfrMsg)=>
             \/ pfrMsg.srcFile#pfuMsg.srcFile
             \/ pfrMsg.destFile#pfuMsg.destFile
             \/ pfrMsg.reservation#MakeParent(pfuMsg.newFile,pfuMsg.newLabel))
     /\ UNCHANGED FileValueTableState
     /\ UNCHANGED FileProtectionTableState
     /\ SendNoMessage
     /\ NoChangeToConsistencyMessageBuffer

(*Defn*)SourceProcessMoveFileOperation==
  \E pfrMsg \in ParentFieldReservedMessage,
     cfrMsg \in ChildFieldReservedMessage,
     opMsg \in MoveFileOperationMessage,
     client \in Client
     :
     /\ WithdrawServerInterlockMessageSet({pfrMsg,cfrMsg})
     /\ DequeueClientConsistencyMessage(opMsg,client)
     /\ opMsg.destinationField=MDSrcParentFile
     /\ pfrMsg.destFile=opMsg.srcParentFile
     /\ pfrMsg.srcFile=opMsg.childFile
     /\ pfrMsg.reservation=MakeParent(opMsg.destParentFile,opMsg.destLabel)
     /\ pfrMsg.initiator=client
     /\ cfrMsg.destFile=opMsg.srcParentFile
     /\ cfrMsg.srcFile=opMsg.destParentFile
     /\ cfrMsg.label=opMsg.destLabel
     /\ cfrMsg.reservation=opMsg.childFile
     /\ cfrMsg.initiator=client
     /\ UNCHANGED FileProtectionTableState
     /\ IF
          /\ ClientKnewChildFile(
               client,opMsg.srcParentFile,opMsg.srcLabel,opMsg.childFile)
          /\ ClientHasWriteChildLease(client,opMsg.srcParentFile,opMsg.srcLabel)
        THEN
          /\ (FileValueTableState')=
             [FileValueTableState EXCEPT
               ![opMsg.srcParentFile].children[opMsg.srcLabel]=Nil
             ]
          /\ ( \E destParentServer \in Server,childServer \in Server:
                  /\ ServerOwnsFile(destParentServer,opMsg.destParentFile)
                  /\ ServerOwnsFile(childServer,opMsg.childFile)
                  /\ SendAddressedMessageSet(
                       {
                       MakeAddressedMessage(
                         destParentServer,
                         MakeUpdateChildFieldMessage(
                           opMsg.destParentFile,
                           opMsg.srcParentFile,
                           opMsg.destLabel,
                           opMsg.childFile,
                           client)),
                       MakeAddressedMessage(
                         childServer,
                         MakeUpdateParentFieldMessage(
                           opMsg.childFile,
                           opMsg.srcParentFile,
                           opMsg.destLabel,
                           opMsg.destParentFile,
                           client))
                       }))
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ SendNoMessage

(*Defn*)ProcessMoveFileOperation==
  /\ NoChangeToFileOwnership
  /\ ( \/ ChildPrepareMoveFileOperation
       \/ ChildCommitMoveFileOperation
       \/ ChildAbortMoveFileOperation
       \/ DestinationPrepareMoveFileOperation
       \/ DestinationCommitMoveFileOperation
       \/ DestinationAbortMoveFileOperation
       \/ DestinationCleanupMoveFileOperation
       \/ DestinationDiscardSpuriousParentFieldUpdatedMessage
       \/ SourceProcessMoveFileOperation)
====
