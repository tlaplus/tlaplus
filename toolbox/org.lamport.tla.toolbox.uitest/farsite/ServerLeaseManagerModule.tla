---- MODULE ServerLeaseManagerModule ----
(*`^\addcontentsline{toc}{section}{ServerLeaseManagerModule}^'*)

EXTENDS
  ServerKnowledgePredicatesModule,
  ServerLeasePartialActionsModule,
  ServerLeaseResourcesModule

(* ********** OpenFile Request ********************************************************************************************* *)

(*Defn*)ProcessOpenFileRequestMessage==
  \E msg \in OpenFileRequestMessage,requester \in Client,withdrawHint \in Boolean:
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF
          \/ ( \E mode \in Mode:
                  /\ ModeOpposite(mode)\in msg.firstModes
                  /\ KnowAnotherClientHasFileMode(requester,msg.fileID,mode))
          \/ KnowFileDeletePending(msg.fileID)
        THEN
          /\ withdrawHint
          /\ ( \/ ( \E mode \in Mode:
                       /\ ModeOpposite(mode)\in msg.firstModes
                       /\ KnowAnotherClientHasFileMode(requester,msg.fileID,mode)
                       /\ GrantOrExtendModeReadOtherLease(requester,msg.fileID,mode,TRUE))
               \/ ( /\ KnowFileDeletePending(msg.fileID)
                    /\ GrantOrExtendSVLease(requester,msg.fileID,FDelDisp,PRead)))
        ELSE IF
          /\ ( \/ KnowFileNotDeletePending(msg.fileID)
               \/ ClientHasWriteSVLease(requester,msg.fileID,FDelDisp))
          /\ KnowAllOtherClientsHaveCompatibleModeSets(requester,msg.fileID,msg.modes)
        THEN
          IF
            /\ ClientHasReadOrWriteSVLease(requester,msg.fileID,FDelDisp)
            /\ ClientHasOpenHandleLease(requester,msg.fileID,BBSelf,PRead)
            /\ ( msg.firstHandle=>
                 ClientHasOpenHandleLease(requester,msg.fileID,BBSelf,PWrite))
            /\ ClientHasBonaFideLease(requester,msg.fileID)
            /\ ( \A mode \in msg.firstModes:ClientHasModeLease(requester,msg.fileID,mode,BBSelf))
          THEN
            /\ withdrawHint
            /\ UNCHANGED FileValueTableState
            /\ UNCHANGED FileProtectionTableState
            /\ SendNoMessage
          ELSE
            /\ (\neg withdrawHint)
            /\ ( \/ ( /\ (\neg ClientHasReadOrWriteSVLease(requester,msg.fileID,FDelDisp))
                      /\ GrantSVLease(requester,msg.fileID,FDelDisp,PRead))
                 \/ ( /\ (\neg ClientHasOpenHandleLease(requester,msg.fileID,BBSelf,PRead))
                      /\ GrantOpenHandleReadSelfLease(requester,msg.fileID))
                 \/ ( /\ msg.firstHandle
                      /\ (\neg ClientHasOpenHandleLease(requester,msg.fileID,BBSelf,PWrite))
                      /\ IF ClientOpenHandleHiddenFromOthers(requester,msg.fileID)
                         THEN
                           GrantOpenHandleWriteSelfLease(requester,msg.fileID)
                         ELSE
                           RecallALeaseToHideClientOpenHandleValue(requester,msg.fileID,msg.priority))
                 \/ ( /\ (\neg ClientHasBonaFideLease(requester,msg.fileID))
                      /\ GrantBonaFideLease(requester,msg.fileID))
                 \/ ( \E mode \in msg.firstModes:
                         /\ (\neg ClientHasModeLease(requester,msg.fileID,mode,BBSelf))
                         /\ IF ClientModeHiddenFromOthers(requester,msg.fileID,mode)
                            THEN
                              GrantModeWriteSelfLease(requester,msg.fileID,mode)
                            ELSE
                              RecallALeaseToHideClientModeValue(requester,msg.fileID,mode,msg.priority)))
        ELSE
          /\ (\neg withdrawHint)
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ ( \/ ( \E client \in Client:
                       /\ client#requester
                       /\ ClientHasIndividualSVLease(
                            client,FileProtectionTableState[msg.fileID].delDisp,PWrite)
                       /\ SendMessage(
                            client,
                            MakeLeaseRecallMessage(
                              MakeFileSharedValueField(msg.fileID,FDelDisp),PWrite,msg.priority)))
               \/ ( \E client \in Client,mode \in msg.modes:
                       /\ client#requester
                       /\ ClientHasIndividualBBLease(
                            client,
                            FileProtectionTableState[msg.fileID].modes[ModeOpposite(mode)],
                            BBSelf,
                            PWrite)
                       /\ SendMessage(
                            client,
                            MakeLeaseRecallMessage(
                              MakeFileModeField(msg.fileID,ModeOpposite(mode),BBSelf),
                              PWrite,
                              msg.priority))))

(* ********** CleanupFile Request ****************************************************************************************** *)

(*Defn*)ProcessCleanupFileRequestMessage==
  \E msg \in CleanupFileRequestMessage,
     requester \in Client,
     withdrawHint \in Boolean
     :
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF
          \A mode \in msg.lastModes:ClientHasModeLease(requester,msg.fileID,mode,BBSelf)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE
          /\ (\neg withdrawHint)
          /\ ( \E mode \in msg.lastModes:
                  /\ (\neg ClientHasModeLease(requester,msg.fileID,mode,BBSelf))
                  /\ IF ClientModeHiddenFromOthers(requester,msg.fileID,mode)
                     THEN
                       GrantModeWriteSelfLease(requester,msg.fileID,mode)
                     ELSE
                       RecallALeaseToHideClientModeValue(requester,msg.fileID,mode,msg.priority))

(* ********** CloseFile Request ******************************************************************************************** *)

(*Defn*)ProcessCloseFileRequestMessage==
  \E msg \in CloseFileRequestMessage,requester \in Client,withdrawHint \in Boolean
     :
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF
          \/ KnowFileNotDeletePending(msg.fileID)
          \/ KnowAnotherClientHasFileOpen(requester,msg.fileID)
        THEN
          IF
            /\ ( \/ ( /\ KnowFileNotDeletePending(msg.fileID)
                      /\ ClientHasReadSVLease(requester,msg.fileID,FDelDisp))
                 \/ ( /\ KnowAnotherClientHasFileOpen(requester,msg.fileID)
                      /\ ClientHasOpenHandleLease(requester,msg.fileID,BBOther,PRead)))
            /\ ClientHasOpenHandleLease(requester,msg.fileID,BBSelf,PWrite)
          THEN
            /\ withdrawHint
            /\ UNCHANGED FileValueTableState
            /\ UNCHANGED FileProtectionTableState
            /\ SendNoMessage
          ELSE
            /\ (\neg withdrawHint)
            /\ ( \/ ( /\ KnowFileNotDeletePending(msg.fileID)
                      /\ (\neg ClientHasReadSVLease(requester,msg.fileID,FDelDisp))
                      /\ GrantSVLease(requester,msg.fileID,FDelDisp,PRead))
                 \/ ( /\ KnowAnotherClientHasFileOpen(requester,msg.fileID)
                      /\ (\neg ClientHasOpenHandleLease(requester,msg.fileID,BBOther,PRead))
                      /\ GrantOpenHandleReadOtherLease(requester,msg.fileID,TRUE))
                 \/ ( /\ (\neg ClientHasOpenHandleLease(requester,msg.fileID,BBSelf,PWrite))
                      /\ IF ClientOpenHandleHiddenFromOthers(requester,msg.fileID)
                         THEN
                           GrantOpenHandleWriteSelfLease(requester,msg.fileID)
                         ELSE
                           RecallALeaseToHideClientOpenHandleValue(requester,msg.fileID,msg.priority)))
        ELSE IF
          /\ ( \/ KnowFileDeletePending(msg.fileID)
               \/ ( /\ ClientHasWriteSVLease(requester,msg.fileID,FDelDisp)
                    /\ ( \A label \in Label:
                            \/ KnowLabelIsUnused(msg.fileID,label)
                            \/ ClientHasWriteChildLease(requester,msg.fileID,label))))
          /\ KnowNoOtherClientHasFileOpen(requester,msg.fileID)
        THEN
          IF
            /\ ClientHasOpenHandleLease(requester,msg.fileID,BBOther,PRead)
            /\ ClientHasOpenHandleLease(requester,msg.fileID,BBSelf,PWrite)
            /\ (\A mode \in Mode:ClientHasModeLease(requester,msg.fileID,mode,BBSelf))
            /\ (\A mode \in Mode:ClientHasModeLease(requester,msg.fileID,mode,BBOther))
            /\ ( \A field \in FSharedValueFields:
                    ClientHasWriteSVLease(requester,msg.fileID,field))
            /\ (\A label \in Label:ClientHasWriteChildLease(requester,msg.fileID,label))
          THEN
            /\ withdrawHint
            /\ UNCHANGED FileValueTableState
            /\ UNCHANGED FileProtectionTableState
            /\ SendNoMessage
          ELSE
            /\ (\neg withdrawHint)
            /\ ( \/ ( /\ (\neg ClientHasOpenHandleLease(requester,msg.fileID,BBOther,PRead))
                      /\ GrantOpenHandleReadOtherLease(requester,msg.fileID,FALSE))
                 \/ ( /\ (\neg ClientHasOpenHandleLease(requester,msg.fileID,BBSelf,PWrite))
                      /\ IF ClientOpenHandleHiddenFromOthers(requester,msg.fileID)
                         THEN
                           GrantOpenHandleWriteSelfLease(requester,msg.fileID)
                         ELSE
                           RecallALeaseToHideClientOpenHandleValue(requester,msg.fileID,msg.priority))
                 \/ ( \E mode \in Mode:
                         /\ (\neg ClientHasModeLease(requester,msg.fileID,mode,BBSelf))
                         /\ IF ClientModeHiddenFromOthers(requester,msg.fileID,mode)
                            THEN
                              GrantModeWriteSelfLease(requester,msg.fileID,mode)
                            ELSE
                              RecallALeaseToHideClientModeValue(requester,msg.fileID,mode,msg.priority))
                 \/ ( \E mode \in Mode:
                         /\ (\neg ClientHasModeLease(requester,msg.fileID,mode,BBOther))
                         /\ IF
                              \A client \in Client:
                                 client#requester=>(\neg ClientHasModeLease(client,msg.fileID,mode,BBSelf))
                            THEN
                              GrantOrExtendModeReadOtherLease(requester,msg.fileID,mode,FALSE)
                            ELSE
                              \E client \in Client:
                                 /\ client#requester
                                 /\ ClientHasIndividualBBLease(
                                      client,FileProtectionTableState[msg.fileID].modes[mode],BBSelf,PWrite)
                                 /\ UNCHANGED FileValueTableState
                                 /\ UNCHANGED FileProtectionTableState
                                 /\ SendMessage(
                                      client,
                                      MakeLeaseRecallMessage(
                                        MakeFileModeField(msg.fileID,mode,BBSelf),PWrite,msg.priority)))
                 \/ ( \E field \in FSharedValueFields:
                         /\ (\neg ClientHasWriteSVLease(requester,msg.fileID,field))
                         /\ IF
                              /\ ( \A client \in Client:
                                      ( \neg ClientHasReadOrWriteSVLease(client,msg.fileID,field)))
                              /\ (field=FParent=>(\neg UpPathLeaseObtained(msg.fileID)))
                            THEN
                              GrantSVLease(requester,msg.fileID,field,PWrite)
                            ELSE
                              \/ ( \E client \in Client,rw \in PReadOrWrite:
                                      /\ ClientHasIndividualSVLease(
                                           client,(FileProtectionTableState[msg.fileID])[field],rw)
                                      /\ UNCHANGED FileValueTableState
                                      /\ UNCHANGED FileProtectionTableState
                                      /\ SendMessage(
                                           client,
                                           MakeLeaseRecallMessage(
                                             MakeFileSharedValueField(msg.fileID,field),rw,msg.priority)))
                              \/ ( /\ field=FParent
                                   /\ UpPathLeaseObtained(msg.fileID)
                                   /\ ReleasePathLease(msg.fileID,msg.priority)))
                 \/ ( /\ (\neg ClientHasInfiniteChildLease(requester,msg.fileID))
                      /\ IF \A client \in Client:(\neg ClientHasInfiniteChildLease(client,msg.fileID))
                         THEN
                           GrantInfiniteChildLease(requester,msg.fileID)
                         ELSE
                           \E client \in Client:
                              /\ ClientHasInfiniteChildLease(client,msg.fileID)
                              /\ UNCHANGED FileValueTableState
                              /\ UNCHANGED FileProtectionTableState
                              /\ SendMessage(
                                   client,
                                   MakeLeaseRecallMessage(
                                     MakeFileInfiniteChildField(msg.fileID,{}),PWrite,msg.priority)))
                 \/ ( \E label \in Label:
                         /\ (\neg ClientHasWriteChildLease(requester,msg.fileID,label))
                         /\ IF
                              \A client \in Client:
                                 ( \neg ClientHasReadOrWriteChildLease(client,msg.fileID,label))
                            THEN
                              GrantSingletonChildLease(requester,msg.fileID,label,PWrite)
                            ELSE
                              \E client \in Client,rw \in PReadOrWrite:
                                 /\ ClientHasIndividualChildLease(client,msg.fileID,label,rw)
                                 /\ UNCHANGED FileValueTableState
                                 /\ UNCHANGED FileProtectionTableState
                                 /\ SendMessage(
                                      client,
                                      MakeLeaseRecallMessage(
                                        MakeFileChildField(msg.fileID,label),rw,msg.priority))))
        ELSE
          /\ (\neg withdrawHint)
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ ( \/ ( \E client \in Client:
                       /\ client#requester
                       /\ ClientHasIndividualSVLease(
                            client,FileProtectionTableState[msg.fileID].delDisp,PWrite)
                       /\ SendMessage(
                            client,
                            MakeLeaseRecallMessage(
                              MakeFileSharedValueField(msg.fileID,FDelDisp),PWrite,msg.priority)))
               \/ ( \E client \in Client:
                       /\ client#requester
                       /\ ClientHasIndividualBBLease(
                            client,FileProtectionTableState[msg.fileID].openHandle,BBSelf,PWrite)
                       /\ SendMessage(
                            client,
                            MakeLeaseRecallMessage(
                              MakeFileOpenHandleField(msg.fileID,BBSelf),PWrite,msg.priority))))

(* ********** ReadFile Request ********************************************************************************************* *)

(*Defn*)ProcessReadFileRequestMessage==
  \E msg \in ReadFileRequestMessage,requester \in Client,withdrawHint \in Boolean:
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF ClientHasReadOrWriteSVLease(requester,msg.fileID,FContent)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE
          /\ (\neg withdrawHint)
          /\ IF
               \A client \in Client:(\neg ClientHasWriteSVLease(client,msg.fileID,FContent))
             THEN
               GrantSVLease(requester,msg.fileID,FContent,PRead)
             ELSE
               \E client \in Client:
                  /\ ClientHasIndividualSVLease(
                       client,FileProtectionTableState[msg.fileID].content,PWrite)
                  /\ UNCHANGED FileValueTableState
                  /\ UNCHANGED FileProtectionTableState
                  /\ SendMessage(
                       client,
                       MakeLeaseRecallMessage(
                         MakeFileSharedValueField(msg.fileID,FContent),PWrite,msg.priority))

(* ********** WriteFile Request ******************************************************************************************** *)

(*Defn*)ProcessWriteFileRequestMessage==
  \E msg \in WriteFileRequestMessage,requester \in Client,withdrawHint \in Boolean
     :
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF ClientHasWriteSVLease(requester,msg.fileID,FContent)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE
          /\ (\neg withdrawHint)
          /\ IF
               \A client \in Client:
                  ( \neg ClientHasReadOrWriteSVLease(client,msg.fileID,FContent))
             THEN
               GrantSVLease(requester,msg.fileID,FContent,PWrite)
             ELSE
               \E client \in Client,rw \in PReadOrWrite:
                  /\ ClientHasIndividualSVLease(
                       client,FileProtectionTableState[msg.fileID].content,rw)
                  /\ UNCHANGED FileValueTableState
                  /\ UNCHANGED FileProtectionTableState
                  /\ SendMessage(
                       client,
                       MakeLeaseRecallMessage(
                         MakeFileSharedValueField(msg.fileID,FContent),rw,msg.priority))

(* ********** CreateFile Request ******************************************************************************************* *)

(*Defn*)ProcessCreateFileRequestMessage==
  \E msg \in CreateFileRequestMessage,
     requester \in Client,
     withdrawHint \in Boolean
     :
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF
          \/ KnowLabelIsUsed(msg.fileID,msg.label)
          \/ KnowFileDeletePending(msg.fileID)
        THEN
          /\ withdrawHint
          /\ ( \/ ( /\ KnowLabelIsUsed(msg.fileID,msg.label)
                    /\ GrantOrExtendSingletonChildLease(requester,msg.fileID,msg.label,PRead))
               \/ ( /\ KnowFileDeletePending(msg.fileID)
                    /\ GrantOrExtendSVLease(requester,msg.fileID,FDelDisp,PRead)))
        ELSE IF
          /\ ( \/ KnowLabelIsUnused(msg.fileID,msg.label)
               \/ ClientHasWriteChildLease(requester,msg.fileID,msg.label))
          /\ ( \/ KnowFileNotDeletePending(msg.fileID)
               \/ ClientHasWriteSVLease(requester,msg.fileID,FDelDisp))
        THEN
          IF
            /\ ClientHasWriteChildLease(requester,msg.fileID,msg.label)
            /\ ClientHasReadOrWriteSVLease(requester,msg.fileID,FDelDisp)
          THEN
            /\ withdrawHint
            /\ UNCHANGED FileValueTableState
            /\ UNCHANGED FileProtectionTableState
            /\ SendNoMessage
          ELSE
            /\ (\neg withdrawHint)
            /\ ( \/ ( /\ (\neg ClientHasWriteChildLease(requester,msg.fileID,msg.label))
                      /\ IF
                           \A client \in Client:
                              ( \neg ClientHasReadOrWriteChildLease(client,msg.fileID,msg.label))
                         THEN
                           GrantSingletonChildLease(requester,msg.fileID,msg.label,PWrite)
                         ELSE
                           \E client \in Client,rw \in PReadOrWrite:
                              /\ ClientHasIndividualChildLease(client,msg.fileID,msg.label,rw)
                              /\ UNCHANGED FileValueTableState
                              /\ UNCHANGED FileProtectionTableState
                              /\ SendMessage(
                                   client,
                                   MakeLeaseRecallMessage(
                                     MakeFileChildField(msg.fileID,msg.label),rw,msg.priority)))
                 \/ ( /\ (\neg ClientHasReadOrWriteSVLease(requester,msg.fileID,FDelDisp))
                      /\ GrantSVLease(requester,msg.fileID,FDelDisp,PRead)))
        ELSE
          /\ (\neg withdrawHint)
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ ( \/ ( \E client \in Client:
                       /\ client#requester
                       /\ ClientHasIndividualChildLease(client,msg.fileID,msg.label,PWrite)
                       /\ SendMessage(
                            client,
                            MakeLeaseRecallMessage(
                              MakeFileChildField(msg.fileID,msg.label),PWrite,msg.priority)))
               \/ ( \E client \in Client:
                       /\ client#requester
                       /\ ClientHasIndividualSVLease(
                            client,FileProtectionTableState[msg.fileID].delDisp,PWrite)
                       /\ SendMessage(
                            client,
                            MakeLeaseRecallMessage(
                              MakeFileSharedValueField(msg.fileID,FDelDisp),PWrite,msg.priority))))

(* ********** DeleteFile Request ******************************************************************************************* *)

(*Defn*)ProcessDeleteFileRequestMessage==
  \E msg \in DeleteFileRequestMessage,
     requester \in Client,
     withdrawHint \in Boolean
     :
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF
          /\ msg.delDisp
          /\ KnowFileHasChildren(msg.fileID)
        THEN
          /\ withdrawHint
          /\ ( \E label \in Label:
                  /\ KnowLabelIsUsed(msg.fileID,label)
                  /\ GrantOrExtendSingletonChildLease(requester,msg.fileID,msg.label,PRead))
        ELSE IF
          msg.delDisp=>
          ( \A label \in Label:
               \/ KnowLabelIsUnused(msg.fileID,label)
               \/ ClientHasWriteChildLease(requester,msg.fileID,label))
        THEN
          IF
            /\ ( msg.delDisp=>
                 ( \A label \in Label:ClientHasReadOrWriteChildLease(requester,msg.fileID,label)))
            /\ ClientHasWriteSVLease(requester,msg.fileID,FDelDisp)
          THEN
            /\ withdrawHint
            /\ UNCHANGED FileValueTableState
            /\ UNCHANGED FileProtectionTableState
            /\ SendNoMessage
          ELSE
            /\ (\neg withdrawHint)
            /\ ( \/ ( /\ msg.delDisp
                      /\ ( \E label \in Label:
                              /\ (\neg ClientHasReadOrWriteChildLease(requester,msg.fileID,label))
                              /\ IF \neg ClientHasInfiniteChildLease(requester,msg.fileID)
                                 THEN
                                   GrantInfiniteChildLease(requester,msg.fileID)
                                 ELSE
                                   GrantSingletonChildLease(requester,msg.fileID,label,PRead)))
                 \/ ( /\ (\neg ClientHasWriteSVLease(requester,msg.fileID,FDelDisp))
                      /\ IF
                           \A client \in Client:
                              ( \neg ClientHasReadOrWriteSVLease(client,msg.fileID,FDelDisp))
                         THEN
                           GrantSVLease(requester,msg.fileID,FDelDisp,PWrite)
                         ELSE
                           \E client \in Client,rw \in PReadOrWrite:
                              /\ ClientHasIndividualSVLease(
                                   client,FileProtectionTableState[msg.fileID].delDisp,rw)
                              /\ UNCHANGED FileValueTableState
                              /\ UNCHANGED FileProtectionTableState
                              /\ SendMessage(
                                   client,
                                   MakeLeaseRecallMessage(
                                     MakeFileSharedValueField(msg.fileID,FDelDisp),rw,msg.priority))))
        ELSE
          /\ (\neg withdrawHint)
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ ( \E client \in Client:
                  /\ client#requester
                  /\ ( \E label \in Label:
                          ClientHasIndividualChildLease(client,msg.fileID,label,PWrite))
                  /\ SendMessage(
                       client,
                       MakeLeaseRecallMessage(
                         MakeFileInfiniteChildField(msg.fileID,{}),PWrite,msg.priority)))

(* ********** MoveFile Request ********************************************************************************************* *)

(*Defn*)ProcessMoveFileRequestMessage==
  \E msg \in MoveFileRequestMessage,requester \in Client,withdrawHint \in Boolean:
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF ClientHasWriteSVLease(requester,msg.fileID,FParent)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE
          /\ (\neg withdrawHint)
          /\ IF
               /\ ( \A client \in Client:
                       ( \neg ClientHasReadOrWriteSVLease(client,msg.fileID,FParent)))
               /\ (\neg UpPathLeaseObtained(msg.fileID))
             THEN
               GrantSVLease(requester,msg.fileID,FParent,PWrite)
             ELSE
               \/ ( \E client \in Client,rw \in PReadOrWrite:
                       /\ ClientHasIndividualSVLease(
                            client,FileProtectionTableState[msg.fileID].parent,rw)
                       /\ UNCHANGED FileValueTableState
                       /\ UNCHANGED FileProtectionTableState
                       /\ SendMessage(
                            client,
                            MakeLeaseRecallMessage(
                              MakeFileSharedValueField(msg.fileID,FParent),rw,msg.priority)))
               \/ ( /\ UpPathLeaseObtained(msg.fileID)
                    /\ ReleasePathLease(msg.fileID,msg.priority))

(* ********** UnlinkChild Request ****************************************************************************************** *)

(*Defn*)ProcessUnlinkChildRequestMessage==
  \E msg \in UnlinkChildRequestMessage,
     requester \in Client,
     withdrawHint \in Boolean
     :
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF ClientHasWriteChildLease(requester,msg.fileID,msg.label)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE
          /\ (\neg withdrawHint)
          /\ IF
               /\ ( \A client \in Client:
                       ( \neg ClientHasReadOrWriteChildLease(client,msg.fileID,msg.label)))
               /\ (\neg DownPathLeaseIssued(msg.fileID,msg.label))
             THEN
               GrantSingletonChildLease(requester,msg.fileID,msg.label,PWrite)
             ELSE
               \/ ( \E client \in Client,rw \in PReadOrWrite:
                       /\ ClientHasIndividualChildLease(client,msg.fileID,msg.label,rw)
                       /\ UNCHANGED FileValueTableState
                       /\ UNCHANGED FileProtectionTableState
                       /\ SendMessage(
                            client,
                            MakeLeaseRecallMessage(
                              MakeFileChildField(msg.fileID,msg.label),rw,msg.priority)))
               \/ ( /\ DownPathLeaseIssued(msg.fileID,msg.label)
                    /\ RecallPathLease(msg.fileID,msg.label,msg.priority))

(* ********** LinkChild Request ******************************************************************************************** *)

(*Defn*)ProcessLinkChildRequestMessage==
  \E msg \in LinkChildRequestMessage,requester \in Client,withdrawHint \in Boolean
     :
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF
          \/ KnowLabelIsUsed(msg.fileID,msg.label)
          \/ KnowFileDeletePending(msg.fileID)
        THEN
          /\ withdrawHint
          /\ ( \/ ( /\ KnowLabelIsUsed(msg.fileID,msg.label)
                    /\ GrantOrExtendSingletonChildLease(requester,msg.fileID,msg.label,PRead))
               \/ ( /\ KnowFileDeletePending(msg.fileID)
                    /\ GrantOrExtendSVLease(requester,msg.fileID,FDelDisp,PRead)))
        ELSE IF
          /\ ( \/ KnowLabelIsUnused(msg.fileID,msg.label)
               \/ ClientHasWriteChildLease(requester,msg.fileID,msg.label))
          /\ ( \/ KnowFileNotDeletePending(msg.fileID)
               \/ ClientHasWriteSVLease(requester,msg.fileID,FDelDisp))
        THEN
          IF
            /\ ClientHasWriteChildLease(requester,msg.fileID,msg.label)
            /\ ClientHasReadOrWriteSVLease(requester,msg.fileID,FDelDisp)
            /\ ClientHasPathWarrant(requester,msg.fileID)
          THEN
            /\ withdrawHint
            /\ UNCHANGED FileValueTableState
            /\ UNCHANGED FileProtectionTableState
            /\ SendNoMessage
          ELSE
            /\ (\neg withdrawHint)
            /\ ( \/ ( /\ (\neg ClientHasWriteChildLease(requester,msg.fileID,msg.label))
                      /\ IF
                           \A client \in Client:
                              ( \neg ClientHasReadOrWriteChildLease(client,msg.fileID,msg.label))
                         THEN
                           GrantSingletonChildLease(requester,msg.fileID,msg.label,PWrite)
                         ELSE
                           \E client \in Client,rw \in PReadOrWrite:
                              /\ ClientHasIndividualChildLease(client,msg.fileID,msg.label,rw)
                              /\ UNCHANGED FileValueTableState
                              /\ UNCHANGED FileProtectionTableState
                              /\ SendMessage(
                                   client,
                                   MakeLeaseRecallMessage(
                                     MakeFileChildField(msg.fileID,msg.label),rw,msg.priority)))
                 \/ ( /\ (\neg ClientHasReadOrWriteSVLease(requester,msg.fileID,FDelDisp))
                      /\ GrantSVLease(requester,msg.fileID,FDelDisp,PRead))
                 \/ ( /\ (\neg ClientHasPathWarrant(requester,msg.fileID))
                      /\ IF UpPathLeaseConfirmed(msg.fileID)
                         THEN
                           GrantPathWarrant(requester,msg.fileID)
                         ELSE
                           \E parentLabel \in Label,parentFile \in FileID,server \in Server:
                              /\ KnowParentFile(msg.fileID,parentLabel,parentFile)
                              /\ ServerOwnsFile(server,parentFile)
                              /\ UNCHANGED FileValueTableState
                              /\ UNCHANGED FileProtectionTableState
                              /\ SendMessage(
                                   server,
                                   MakePathRequestMessage(parentFile,msg.destFile,msg.priority,parentLabel))))
        ELSE
          /\ (\neg withdrawHint)
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ ( \/ ( \E client \in Client:
                       /\ client#requester
                       /\ ClientHasIndividualChildLease(client,msg.fileID,msg.label,PWrite)
                       /\ SendMessage(
                            client,
                            MakeLeaseRecallMessage(
                              MakeFileChildField(msg.fileID,msg.label),PWrite,msg.priority)))
               \/ ( \E client \in Client:
                       /\ client#requester
                       /\ ClientHasIndividualSVLease(
                            client,FileProtectionTableState[msg.fileID].delDisp,PWrite)
                       /\ SendMessage(
                            client,
                            MakeLeaseRecallMessage(
                              MakeFileSharedValueField(msg.fileID,FDelDisp),PWrite,msg.priority))))

(* ********** ResolveLabel Request ***************************************************************************************** *)

(*Defn*)ProcessResolveLabelRequestMessage==
  \E msg \in ResolveLabelRequestMessage,
     requester \in Client,
     withdrawHint \in Boolean
     :
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF
          /\ ClientHasReadChildLease(requester,msg.fileID,msg.label)
          /\ ( \A childFile \in FileID:
                  /\ KnowChildFile(msg.fileID,msg.label,childFile)
                  /\ ServerOwnsFile(thisHost,childFile)
                  =>
                  ClientHasReadSVLease(requester,childFile,FParent))
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE
          /\ (\neg withdrawHint)
          /\ ( \/ ( /\ (\neg ClientHasReadChildLease(requester,msg.fileID,msg.label))
                    /\ IF
                         /\ (\neg FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester))
                         /\ ( \A client \in Client:
                                 ( \neg ClientHasWriteChildLease(client,msg.fileID,msg.label)))
                       THEN
                         GrantSingletonChildLease(requester,msg.fileID,msg.label,PRead)
                       ELSE
                         \E client \in Client:
                            /\ ( \/ ( /\ client=requester
                                      /\ FileHasBeenTransitivelyBorrowedByClient(msg.fileID,client))
                                 \/ ClientHasIndividualChildLease(client,msg.fileID,msg.label,PWrite))
                            /\ UNCHANGED FileValueTableState
                            /\ UNCHANGED FileProtectionTableState
                            /\ SendMessage(
                                 client,
                                 MakeLeaseRecallMessage(
                                   MakeFileChildField(msg.fileID,msg.label),PWrite,msg.priority)))
               \/ ( \E childFile \in FileID:
                       /\ KnowChildFile(msg.fileID,msg.label,childFile)
                       /\ ServerOwnsFile(thisHost,childFile)
                       /\ (\neg ClientHasReadSVLease(requester,childFile,FParent))
                       /\ IF
                            \A client \in Client:(\neg ClientHasWriteSVLease(client,childFile,FParent))
                          THEN
                            GrantSVLease(requester,childFile,FParent,PRead)
                          ELSE
                            \E client \in Client:
                               /\ ClientHasIndividualSVLease(
                                    client,FileProtectionTableState[childFile].parent,PWrite)
                               /\ UNCHANGED FileValueTableState
                               /\ UNCHANGED FileProtectionTableState
                               /\ SendMessage(
                                    client,
                                    MakeLeaseRecallMessage(
                                      MakeFileSharedValueField(childFile,FParent),PWrite,msg.priority))))

(* ********** IdentifyParent Request *************************************************************************************** *)

(*Defn*)ProcessIdentifyParentRequestMessage==
  \E msg \in IdentifyParentRequestMessage,
     requester \in Client,
     withdrawHint \in Boolean
     :
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,withdrawHint)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF
          /\ ClientHasReadSVLease(requester,msg.fileID,FParent)
          /\ ( \A parentFile \in FileID,label \in Label:
                  /\ KnowParentFile(msg.fileID,label,parentFile)
                  /\ ServerOwnsFile(thisHost,parentFile)
                  =>
                  ClientHasReadChildLease(requester,parentFile,label))
        THEN
          /\ withdrawHint
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE
          /\ (\neg withdrawHint)
          /\ ( \/ ( /\ (\neg ClientHasReadSVLease(requester,msg.fileID,FParent))
                    /\ IF
                         /\ (\neg FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester))
                         /\ ( \A client \in Client:(\neg ClientHasWriteSVLease(client,msg.fileID,FParent)))
                       THEN
                         GrantSVLease(requester,msg.fileID,FParent,PRead)
                       ELSE
                         \E client \in Client:
                            /\ ( \/ ( /\ client=requester
                                      /\ FileHasBeenTransitivelyBorrowedByClient(msg.fileID,client))
                                 \/ ClientHasIndividualSVLease(
                                      client,FileProtectionTableState[msg.fileID].parent,PWrite))
                            /\ UNCHANGED FileValueTableState
                            /\ UNCHANGED FileProtectionTableState
                            /\ SendMessage(
                                 client,
                                 MakeLeaseRecallMessage(
                                   MakeFileSharedValueField(msg.fileID,FParent),PWrite,msg.priority)))
               \/ ( \E parentFile \in FileID,label \in Label:
                       /\ KnowParentFile(msg.fileID,label,parentFile)
                       /\ ServerOwnsFile(thisHost,parentFile)
                       /\ (\neg ClientHasReadChildLease(requester,parentFile,label))
                       /\ IF
                            \A client \in Client:(\neg ClientHasWriteChildLease(client,parentFile,label))
                          THEN
                            GrantSingletonChildLease(requester,parentFile,label,PRead)
                          ELSE
                            \E client \in Client:
                               /\ ClientHasIndividualChildLease(client,parentFile,label,PWrite)
                               /\ UNCHANGED FileValueTableState
                               /\ UNCHANGED FileProtectionTableState
                               /\ SendMessage(
                                    client,
                                    MakeLeaseRecallMessage(
                                      MakeFileChildField(parentFile,label),PWrite,msg.priority))))

(* ********** Lease-Extension Request ************************************************************************************** *)

(*Defn*)ProcessLeaseExtensionRequestMessage==
  \E msg \in LeaseExtensionRequestMessage,requester \in Client:
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,TRUE)
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF
          /\ msg.fileField \in FileSharedValueFields
          /\ ClientHasIndividualSVLease(
               requester,
               (FileProtectionTableState[msg.fileField.fileID])[msg.fileField.field],
               msg.rw)
        THEN
          GrantOrExtendSVLease(
            requester,msg.fileField.fileID,msg.fileField.field,msg.rw)
        ELSE IF
          /\ msg.fileField \in FileChildField
          /\ ClientHasIndividualChildLease(
               requester,msg.fileField.fileID,msg.fileField.label,msg.rw)
        THEN
          IF
            ClientHasInfiniteChildLeaseOnLabel(
              requester,msg.fileField.fileID,msg.fileField.label)
          THEN
            ExtendInfiniteChildLease(requester,msg.fileField.fileID)
          ELSE
            GrantOrExtendSingletonChildLease(
              requester,msg.fileField.fileID,msg.fileField.label,msg.rw)
        ELSE IF
          /\ msg.fileField \in FileOpenHandleField
          /\ (\neg(msg.fileField.so=BBOther/\ msg.rw=PWrite))
          /\ ClientHasIndividualBBLease(
               requester,
               FileProtectionTableState[msg.fileField.fileID].openHandle,
               msg.fileField.so,
               msg.rw)
        THEN
          ExtendOpenHandleLease(requester,msg.fileField.fileID,msg.fileField.so,msg.rw)
        ELSE IF
          /\ msg.fileField \in FileBonaFideField
          /\ msg.rw=PRead
          /\ ClientHasIndividualPVLease(
               requester,FileProtectionTableState[msg.fileField.fileID].bonaFide)
        THEN
          ExtendBonaFideLease(requester,msg.fileField.fileID)
        ELSE IF
          /\ msg.fileField \in FileModeField
          /\ ( \/ (msg.fileField.so=BBSelf/\ msg.rw=PWrite)
               \/ (msg.fileField.so=BBOther/\ msg.rw=PRead))
          /\ ClientHasIndividualBBLease(
               requester,
               FileProtectionTableState[msg.fileField.fileID].modes[msg.fileField.mode],
               msg.fileField.so,
               msg.rw)
        THEN
          ExtendModeLease(
            requester,msg.fileField.fileID,msg.fileField.mode,msg.fileField.so,msg.rw)
        ELSE IF
          /\ msg.fileField \in FilePathField
          /\ msg.rw=PRead
          /\ ClientHasPathWarrant(requester,msg.fileField.fileID)
        THEN
          ExtendPathWarrant(requester,msg.fileField.fileID)
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage

(* ********** OpenHandle Read Self Request ********************************************************************************* *)

(* 
	TODO JD jonh notes that ProcessOpenHandleReadSelfRequestMessage and
	ProcessBonaFideRequestMessage don't check
	SomeServerMessageHasPriorityOverMessage. That makes sense; the client doesn't
	send these messages in response to a user request. But the result
	is that these requests receive highest priority. That seems to suggest
	a malicious client could DDOS the server by sending lots of requests
	for these, scooping other client requests. I guess.
 *)

(*Defn*)ProcessOpenHandleReadSelfRequestMessage==
  \E msg \in OpenHandleReadSelfRequestMessage,requester \in Client:
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,TRUE)
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF
          ClientHasIndividualBBLease(
            requester,FileProtectionTableState[msg.fileID].openHandle,BBSelf,PRead)
        THEN
          ExtendOpenHandleLease(requester,msg.fileID,BBSelf,PRead)
        ELSE IF \neg FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          GrantOpenHandleReadSelfLease(requester,msg.fileID)
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage

(* ********** BonaFide Request ********************************************************************************************* *)

(*Defn*)ProcessBonaFideRequestMessage==
  \E msg \in BonaFideRequestMessage,requester \in Client:
     /\ ConditionallyWithdrawLeaseRequestMessage(msg,requester,TRUE)
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ IF
          ClientHasIndividualPVLease(
            requester,FileProtectionTableState[msg.fileID].bonaFide)
        THEN
          ExtendBonaFideLease(requester,msg.fileID)
        ELSE IF \neg FileHasBeenTransitivelyBorrowedByClient(msg.fileID,requester)
        THEN
          GrantBonaFideLease(requester,msg.fileID)
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage

(* ********** Process Path Messages **************************************************************************************** *)

(*Defn*)ProcessPathRequestMessage==
  \E msg \in PathRequestMessage:
     /\ MessageInServerInterlockBuffer(msg)
     /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToLeaseRequestMessageBuffer
     /\ IF/\ DownPathLeaseIssued(msg.destFile,msg.label)
        THEN
          /\ WithdrawServerInterlockMessageSet({msg})
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE
          /\ NoChangeToInterlockMessageBuffer
          /\ IF
               /\ KnowChildFile(msg.destFile,msg.label,msg.srcFile)
               /\ UpPathLeaseConfirmed(msg.destFile)
             THEN
               GrantOrExtendPathLease(msg.destFile,msg.label)
             ELSE
               /\ UNCHANGED FileValueTableState
               /\ UNCHANGED FileProtectionTableState
               /\ ( \/ ( \E client \in Client:
                            /\ ClientHasIndividualChildLease(client,msg.destFile,msg.label,PWrite)
                            /\ SendMessage(
                                 client,
                                 MakeLeaseRecallMessage(
                                   MakeFileChildField(msg.destFile,msg.label),PWrite,msg.priority)))
                    \/ ( \E client \in Client:
                            /\ ClientHasIndividualSVLease(
                                 client,FileProtectionTableState[msg.destFile].parent,PWrite)
                            /\ SendMessage(
                                 client,
                                 MakeLeaseRecallMessage(
                                   MakeFileSharedValueField(msg.destFile,FParent),PWrite,msg.priority)))
                    \/ ( \E parentLabel \in Label,parentFile \in FileID,server \in Server:
                            /\ (\neg UpPathLeaseConfirmed(msg.destFile))
                            /\ KnowParentFile(msg.destFile,parentLabel,parentFile)
                            /\ ServerOwnsFile(server,parentFile)
                            /\ SendMessage(
                                 server,
                                 MakePathRequestMessage(parentFile,msg.destFile,msg.priority,parentLabel))))

(*Defn*)ProcessPathGrantMessage==
  \E msg \in PathGrantMessage:
     /\ WithdrawServerInterlockMessageSet({msg})
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToLeaseRequestMessageBuffer
     /\ IF
          /\ (\neg msg.extension)
          /\ UpPathLeaseConfirmed(msg.destFile)
        THEN
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF
          /\ msg.extension
          /\ ReturnedUpPathLease(msg.destFile)
        THEN
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF
          \A client \in Client:(\neg ClientHasWriteSVLease(client,msg.destFile,FParent))
        THEN
          /\ (FileValueTableState')=
             IF msg.extension
             THEN
               FileValueTableState
             ELSE
               [FileValueTableState EXCEPT![msg.destFile].path=msg.ancestors]
          /\ (FileProtectionTableState')=
             [FileProtectionTableState EXCEPT![msg.destFile].path.up=msg.expiration]
          /\ SendNoMessage
        ELSE
          \E server \in Server:
             /\ ServerOwnsFile(server,msg.srcFile)
             /\ UNCHANGED FileValueTableState
             /\ UNCHANGED FileProtectionTableState
             /\ SendMessage(
                  server,MakePathReleaseMessage(msg.srcFile,msg.destFile,msg.expiration))

(*Defn*)ProcessPathRecallMessage==
  \E msg \in PathRecallMessage:
     \/ ( /\ MessageInServerInterlockBuffer(msg)
          /\ UpPathLeaseObtained(msg.destFile)
          /\ (\neg SomeServerMessageHasPriorityOverMessage(msg))
          /\ ReleasePathLease(msg.destFile,msg.priority)
          /\ NoChangeToConsistencyMessageBuffer
          /\ NoChangeToLeaseRequestMessageBuffer
          /\ NoChangeToInterlockMessageBuffer)
     \/ ( /\ WithdrawServerInterlockMessageSet({msg})
          /\ NoChangeToConsistencyMessageBuffer
          /\ NoChangeToLeaseRequestMessageBuffer
          /\ (\neg UpPathLeaseObtained(msg.destFile))
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage)

(*Defn*)ProcessPathReleaseMessage==
  \E msg \in PathReleaseMessage:
     /\ WithdrawServerInterlockMessageSet({msg})
     /\ NoChangeToConsistencyMessageBuffer
     /\ NoChangeToLeaseRequestMessageBuffer
     /\ IF
          \A label \in Label:
             \/ (\neg KnowChildFile(msg.destFile,label,msg.srcFile))
             \/ (\neg DownPathLeaseIssued(msg.destFile,label))
        THEN
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE
          \E label \in Label:
             /\ KnowChildFile(msg.destFile,label,msg.srcFile)
             /\ DownPathLeaseIssued(msg.destFile,label)
             /\ UNCHANGED FileValueTableState
             /\ (FileProtectionTableState')=
                [FileProtectionTableState EXCEPT
                  ![msg.destFile].path.down[label]=BeforeTimeBegins
                ]
             /\ SendNoMessage

(* ********** Lease Release ************************************************************************************************ *)

(*Defn*)ProcessLeaseReleaseMessage==
  \E msg \in LeaseReleaseMessage,client \in Client:
     /\ DequeueClientConsistencyMessage(msg,client)
     /\ NoChangeToLeaseRequestMessageBuffer
     /\ NoChangeToInterlockMessageBuffer
     /\ UNCHANGED FileValueTableState
     /\ (FileProtectionTableState')=
        [FileProtectionTableState EXCEPT
          ![msg.fileField.fileID]=
            IF msg.fileField \in FileSharedValueFields
            THEN
              [@EXCEPT![msg.fileField.field].individual[client][msg.rw]=BeforeTimeBegins]
            ELSE IF msg.fileField \in FileChildField
            THEN
              [@EXCEPT
                !.children.singleton[msg.fileField.label].individual[client][msg.rw]=
                  BeforeTimeBegins,
                !.children.infinite=
                  IF@.client=client
                  THEN
                    [@EXCEPT!.excludedLabels=(@\union{msg.fileField.label})]
                  ELSE
                    @
              ]
            ELSE IF msg.fileField \in FileOpenHandleField
            THEN
              [@EXCEPT
                !.openHandle[msg.fileField.so].individual[client][msg.rw]=BeforeTimeBegins
              ]
            ELSE IF msg.fileField \in FileBonaFideField
            THEN
              [@EXCEPT!.bonaFide.individual[client].read=BeforeTimeBegins]
            ELSE IF msg.fileField \in FileModeField
            THEN
              [@EXCEPT
                !.modes[msg.fileField.mode][msg.fileField.so].individual[client][msg.rw]=
                  BeforeTimeBegins
              ]
            ELSE IF msg.fileField \in FileAccessField
            THEN
              [@EXCEPT
                !.accesses[msg.fileField.access].individual[client].read=BeforeTimeBegins
              ]
            ELSE IF msg.fileField \in FilePathField
            THEN
              [@EXCEPT!.path.individual[client].read=BeforeTimeBegins]
            ELSE IF msg.fileField \in FileInfiniteChildField
            THEN
              [@EXCEPT
                !.children.infinite=
                  IF@.client=client THEN InfiniteChild({},Nil,BeforeTimeBegins)ELSE@,
                !.children.singleton=
                  [label \in Label|->
                    [@[label]EXCEPT
                      !.individual[client]=
                        [rw \in PReadOrWrite|->
                          IF label \in msg.fileField.excludedLabels
                          THEN
                            ClientIndividualChildLeaseExpirationTime(
                              client,msg.fileField.fileID,label,rw)
                          ELSE
                            BeforeTimeBegins
                        ]
                    ]
                  ]
              ]
            ELSE
              @
        ]
     /\ SendMessage(client,MakePositiveAcknowledgementMessage(msg.ackID))
====
