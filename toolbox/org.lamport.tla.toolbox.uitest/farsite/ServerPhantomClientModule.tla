---- MODULE ServerPhantomClientModule ----
(*`^\addcontentsline{toc}{section}{ServerPhantomClientModule}^'*)

EXTENDS
  ServerKnowledgePredicatesModule,
  ServerMessageBuffersModule,
  ServerLeasePartialActionsModule
(*Defn*)PerformPhantomCleanupFile==
  \E fileID \in FileID,handle \in Handle,delinquent \in Client:
     LET
       (*Defn*)lastModes==
         {mode \in Mode:
           (FileValueTableState[fileID].modes[mode].self[delinquent]={handle})
         }
     IN
       /\ CanSpontaneouslyCleanupClientHandleOnFile(delinquent,handle,fileID)
       /\ NoChangeToInterlockMessageBuffer
       /\ IF \A mode \in lastModes:ClientModeHiddenFromOthers(delinquent,fileID,mode)
          THEN
            /\ (FileValueTableState')=
               [
                 [FileValueTableState EXCEPT![fileID].bonaFide[delinquent]=(@\ {handle})]
               EXCEPT
                 ![fileID]=
                   [@EXCEPT
                     !.modes=
                       [mode \in DOMAIN@|->
                         IF mode \in Mode
                         THEN
                           LET
                             (*Defn*)AtSymbol001==@[mode]
                           IN
                             [AtSymbol001 EXCEPT!.self[delinquent]=(@\ {handle})]
                         ELSE
                           @[mode]
                       ]
                   ]
               ]
            /\ UNCHANGED FileProtectionTableState
            /\ SendNoMessage
          ELSE
            \E mode \in lastModes:
               /\ (\neg ClientModeHiddenFromOthers(delinquent,fileID,mode))
               /\ RecallALeaseToHideClientModeValue(delinquent,fileID,mode,AfterTimeEnds)

(*Defn*)ChildPerformOrPreparePhantomCloseFile==
  \E fileID \in FileID,handle \in Handle,delinquent \in Client:
     LET
       (*Defn*)lastHandle==
         FileValueTableState[fileID].openHandle.self[delinquent]={handle}
     IN
       /\ CanSpontaneouslyCloseClientHandleOnFile(delinquent,handle,fileID)
       /\ NoChangeToInterlockMessageBuffer
       /\ IF
            \/ (\neg lastHandle)
            \/ KnowFileNotDeletePending(fileID)
            \/ KnowAnotherClientHasFileOpen(delinquent,fileID)
          THEN
            IF lastHandle=>ClientOpenHandleHiddenFromOthers(delinquent,fileID)
            THEN
              /\ (FileValueTableState')=
                 [
                   [FileValueTableState EXCEPT
                     ![fileID].openHandle.self[delinquent]=(@\ {handle})
                   ]
                 EXCEPT
                   ![fileID]=
                     [@EXCEPT
                       !.accesses=
                         [access \in DOMAIN@|->
                           IF access \in Access
                           THEN
                             LET
                               (*Defn*)AtSymbol002==@[access]
                             IN
                               [AtSymbol002 EXCEPT![delinquent]=(@\ {handle})]
                           ELSE
                             @[access]
                         ]
                     ]
                 ]
              /\ UNCHANGED FileProtectionTableState
              /\ SendNoMessage
            ELSE
              /\ lastHandle
              /\ (\neg ClientOpenHandleHiddenFromOthers(delinquent,fileID))
              /\ RecallALeaseToHideClientOpenHandleValue(delinquent,fileID,AfterTimeEnds)
          ELSE IF
            /\ lastHandle
            /\ KnowFileDeletePending(fileID)
            /\ KnowNoOtherClientHasFileOpen(delinquent,fileID)
          THEN
            IF
              /\ ClientOpenHandleHiddenFromOthers(delinquent,fileID)
              /\ ( \A field \in FSharedValueFields,client \in Client:
                      ( \neg ClientHasReadOrWriteSVLease(client,fileID,field)))
              /\ (\neg UpPathLeaseObtained(fileID))
              /\ ( \A label \in Label,client \in Client:
                      ( \neg ClientHasReadOrWriteChildLease(client,fileID,label)))
            THEN
              \E parentFile \in FileID,label \in Label:
                 /\ KnowParentFile(fileID,label,parentFile)
                 /\ UNCHANGED FileValueTableState
                 /\ (FileProtectionTableState')=
                    [FileProtectionTableState EXCEPT
                      ![fileID].parent.reservation=
                        Reservation(delinquent,parentFile,MakeParent(Nil,Nil))
                    ]
                 /\ ( \E parentServer \in Server,expirationTime \in ServerInterlockTimeRange:
                         /\ ServerOwnsFile(parentServer,parentFile)
                         /\ SendMessage(
                              parentServer,
                              MakeUpdateChildFieldMessage(parentFile,fileID,label,Nil,delinquent)))
            ELSE
              \/ ( /\ (\neg ClientOpenHandleHiddenFromOthers(delinquent,fileID))
                   /\ RecallALeaseToHideClientOpenHandleValue(delinquent,fileID,AfterTimeEnds))
              \/ ( \E field \in FSharedValueFields,client \in Client,rw \in PReadOrWrite:
                      /\ ClientHasIndividualSVLease(
                           client,(FileProtectionTableState[fileID])[field],rw)
                      /\ UNCHANGED FileValueTableState
                      /\ UNCHANGED FileProtectionTableState
                      /\ SendMessage(
                           client,
                           MakeLeaseRecallMessage(
                             MakeFileSharedValueField(fileID,field),rw,AfterTimeEnds)))
              \/ ( /\ UpPathLeaseObtained(fileID)
                   /\ ReleasePathLease(fileID,AfterTimeEnds))
              \/ ( \E client \in Client:
                      /\ ClientHasInfiniteChildLease(client,fileID)
                      /\ UNCHANGED FileValueTableState
                      /\ UNCHANGED FileProtectionTableState
                      /\ SendMessage(
                           client,
                           MakeLeaseRecallMessage(
                             MakeFileInfiniteChildField(fileID,{}),PWrite,AfterTimeEnds)))
              \/ ( \E label \in Label,client \in Client,rw \in PReadOrWrite:
                      /\ ClientHasIndividualChildLease(client,fileID,label,rw)
                      /\ UNCHANGED FileValueTableState
                      /\ UNCHANGED FileProtectionTableState
                      /\ SendMessage(
                           client,
                           MakeLeaseRecallMessage(MakeFileChildField(fileID,label),rw,AfterTimeEnds)))
          ELSE
            /\ UNCHANGED FileValueTableState
            /\ UNCHANGED FileProtectionTableState
            /\ ( \/ ( \E client \in Client:
                         /\ ClientHasIndividualSVLease(
                              client,FileProtectionTableState[fileID].delDisp,PWrite)
                         /\ SendMessage(
                              client,
                              MakeLeaseRecallMessage(MakeFileDelDispField(fileID),PWrite,AfterTimeEnds)))
                 \/ ( \E client \in Client:
                         /\ ClientHasIndividualBBLease(
                              client,FileProtectionTableState[fileID].openHandle,BBSelf,PWrite)
                         /\ SendMessage(
                              client,
                              MakeLeaseRecallMessage(
                                MakeFileOpenHandleField(fileID,BBSelf),PWrite,AfterTimeEnds))))

(*Defn*)ChildCommitPhantomCloseAndUnlinkFile==
  \E cfuMsg \in ChildFieldUpdatedMessage,handle \in Handle,delinquent \in Client:
     /\ WithdrawServerInterlockMessageSet({cfuMsg})
     /\ cfuMsg.newFile=Nil
     /\ SendNoMessage
     /\ IF
          /\ KnowParentFile(cfuMsg.destFile,cfuMsg.label,cfuMsg.srcFile)
          /\ FileProtectionTableState[cfuMsg.destFile].parent.reservation.leader=
             cfuMsg.srcFile
          /\ FileProtectionTableState[cfuMsg.destFile].parent.reservation.value=
             MakeParent(Nil,Nil)
        THEN
          /\ (FileValueTableState')=
             [FileValueTableState EXCEPT![cfuMsg.destFile]=FileValueInit]
          /\ (FileProtectionTableState')=
             [FileProtectionTableState EXCEPT
               ![cfuMsg.destFile]=
                 [FileProtectionInit EXCEPT
                   !.maxSuffix=FileProtectionTableState[cfuMsg.destFile].maxSuffix
                 ]
             ]
        ELSE
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState

(*Defn*)ParentProcessPhantomCloseAndUnlinkFile==
  \E ucfMsg \in UpdateChildFieldMessage,childServer \in Server:
     /\ MessageInServerInterlockBuffer(ucfMsg)
     /\ ServerOwnsFile(childServer,ucfMsg.srcFile)
     /\ ucfMsg.newFile=Nil
     /\ IF
          \E fileID \in NilOr(FileID):
             /\ fileID#ucfMsg.srcFile
             /\ KnowChildFile(ucfMsg.destFile,ucfMsg.label,fileID)
        THEN
          /\ WithdrawServerInterlockMessageSet({ucfMsg})
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendNoMessage
        ELSE IF
          /\ KnowChildFile(ucfMsg.destFile,ucfMsg.label,ucfMsg.srcFile)
          /\ ( \A client \in Client:
                  ( \neg ClientHasReadOrWriteChildLease(client,ucfMsg.destFile,ucfMsg.label)))
          /\ (\neg DownPathLeaseIssued(ucfMsg.destFile,ucfMsg.label))
        THEN
          /\ WithdrawServerInterlockMessageSet({ucfMsg})
          /\ (FileValueTableState')=
             [FileValueTableState EXCEPT![ucfMsg.destFile].children[ucfMsg.label]=Nil]
          /\ UNCHANGED FileProtectionTableState
          /\ SendMessage(
               childServer,
               MakeChildFieldUpdatedMessage(
                 ucfMsg.srcFile,ucfMsg.destFile,ucfMsg.label,Nil))
        ELSE
          /\ NoChangeToInterlockMessageBuffer
          /\ ( \/ ( \E client \in Client,rw \in PReadOrWrite:
                       /\ ClientHasIndividualChildLease(client,ucfMsg.destFile,ucfMsg.label,rw)
                       /\ UNCHANGED FileValueTableState
                       /\ UNCHANGED FileProtectionTableState
                       /\ SendMessage(
                            client,
                            MakeLeaseRecallMessage(
                              MakeFileChildField(ucfMsg.destFile,ucfMsg.label),rw,AfterTimeEnds)))
               \/ ( /\ DownPathLeaseIssued(ucfMsg.destFile,ucfMsg.label)
                    /\ RecallPathLease(ucfMsg.destFile,ucfMsg.label,AfterTimeEnds)))
====
