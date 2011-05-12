---- MODULE foo1 ----
(*`^\addcontentsline{toc}{section}{ClientOperationProcessorModule}^'*)

EXTENDS
  ClientKnowledgePredicatesModule,ClientFileOwnershipModule,ThreadModule
(* ********** Predicates *************************************************************************************************** *)

(*Defn*)HandleIsAvailable(handle)==
  /\ ( \A fileID \in FileID:
          handle \notin FileValueTableState[fileID].openHandle.self[thisHost])
  /\ KnowHandleClosingNotInProgress(handle)

(* ********** Partial Actions ********************************************************************************************** *)

(*Defn*)ReturnSuccess(thread,value)==
  /\ NoChangeToFileMap
  /\ SendNoMessage
  /\ ThreadReturn(thread,[rc|->RCSuccess,value|->value])

(*Defn*)ReturnArbitraryFailure(thread)==
  /\ NoChangeToFileOwnership
  /\ UNCHANGED ActiveProtectionRecords
  /\ UNCHANGED FileValueTableState
  /\ NoChangeToMessageLog
  /\ SendNoMessage
  /\ ThreadReturn(thread,[rc|->RCErrorArbitrary])

(*Defn*)ReturnSpecificFailure(thread,rc)==
  /\ NoChangeToFileOwnership
  /\ UNCHANGED ActiveProtectionRecords
  /\ UNCHANGED FileValueTableState
  /\ NoChangeToMessageLog
  /\ SendNoMessage
  /\ ThreadReturn(thread,[rc|->rc])

(*Defn*)NoReturn==
  /\ NoChangeToFileMap
  /\ UNCHANGED ActiveProtectionRecords
  /\ UNCHANGED FileValueTableState
  /\ ThreadNoReturn

(*Defn*)ResolveNextPathStep(rootFile,labelPath,priority)==
  \E filePath \in FileSeq:
     LET
       (*Defn*)lastFile==filePath[Len(filePath)]
       (*Defn*)lastLabel==labelPath[Len(filePath)]
     IN
       /\ filePath#<<>>
       /\ Len(filePath)\leq Len(labelPath)
       /\ rootFile=First(filePath)
       /\ KnowPrefixOfLabelPathConnectsFilePath(labelPath,filePath)
       /\ UNCHANGED ActiveBorrowerRecords
       /\ NoChangeToMessageLog
       /\ IF \neg HaveReadOrWriteChildLease(lastFile,lastLabel)
          THEN
            \E server \in Server:
               /\ ServerOwnsFile(server,lastFile)
               /\ SendMessage(
                    server,
                    MakeResolveLabelRequestMessage(
                      lastFile,MakeDistributedPriority(priority,thisHost),lastLabel))
          ELSE
            \E childFile \in FileID,server \in Server:
               /\ KnowChildFile(lastFile,lastLabel,childFile)
               /\ (\neg HaveReadOrWriteSVLease(childFile,FParent))
               /\ ServerOwnsFile(server,childFile)
               /\ SendMessage(
                    server,
                    MakeIdentifyParentRequestMessage(
                      childFile,MakeDistributedPriority(priority,thisHost)))

(*Defn*)ResolvePreviousPathStep(fileID,priority)==
  \E firstFile \in FileID,labelPath \in LabelSeq:
     /\ firstFile#FilesystemRoot
     /\ KnowPathResolvesToTarget(firstFile,labelPath,fileID)
     /\ UNCHANGED ActiveBorrowerRecords
     /\ NoChangeToMessageLog
     /\ IF \neg HaveReadSVLease(firstFile,FParent)
        THEN
          \E server \in Server:
             /\ ServerOwnsFile(server,firstFile)
             /\ SendMessage(
                  server,
                  MakeIdentifyParentRequestMessage(
                    firstFile,MakeDistributedPriority(priority,thisHost)))
        ELSE
          \E parentFile \in FileID,label \in Label,server \in Server:
             /\ KnowParentFile(firstFile,label,parentFile)
             /\ (\neg HaveReadChildLease(parentFile,label))
             /\ ServerOwnsFile(server,parentFile)
             /\ SendMessage(
                  server,
                  MakeResolveLabelRequestMessage(
                    parentFile,MakeDistributedPriority(priority,thisHost),label))

(* ********** Open File **************************************************************************************************** *)

(*  TODO JD jonh: I think there's a persistent bug throughout this file (and maybe
elsewhere in the spec) where request.modeSet is referred to as request.modes.
 *)

(*Defn*)PerformOpenFileOperation==
  \E thread \in Thread,req \in Request:
     /\ IsRequestReady(thread,req)
     /\ req.cmd=CmdOpen
     /\ IF
          \A rootFile \in FileID:
             \/ KnowHandleNotOpenOnFile(req.handle,rootFile)
             \/ KnowHandleOnFileNotBonaFide(req.handle,rootFile)
        THEN
          ReturnArbitraryFailure(thread)
        ELSE
          \E rootFile \in FileID:
             /\ KnowHandleOpenOnFile(req.handle,rootFile)
             /\ KnowHandleOnFileIsBonaFide(req.handle,rootFile)
             /\ IF KnowPathDoesNotResolve(rootFile,req.path)
                THEN
                  ReturnArbitraryFailure(thread)
                ELSE IF
                  \A fileID \in FileID:(\neg KnowPathResolvesToTarget(rootFile,req.path,fileID))
                THEN
                  /\ NoReturn
                  /\ ResolveNextPathStep(rootFile,req.path,req.priority)
                ELSE
                  \E fileID \in FileID:
                     LET
                       (*Defn*)firstModes==
                         {mode \in req.modes:KnowNoHandleHasModeOnFile(mode,fileID)}
                       (*Defn*)reqAccesses==ModeSetToAccessSet(req.modes)
                     IN
                       /\ KnowPathResolvesToTarget(rootFile,req.path,fileID)
                       /\ IF KnowModeSetConflicts(fileID,req.modes)
                          THEN
                            ReturnArbitraryFailure(thread)
                          ELSE IF KnowFileDeletePending(fileID)
                          THEN
                            ReturnArbitraryFailure(thread)
                          ELSE IF
                            /\ KnowModeSetCompatible(fileID,req.modes)
                            /\ KnowFileNotDeletePending(fileID)
                            /\ ( \/ ( /\ KnowNoHandleOpenOnFile(fileID)
                                      /\ KnowCanOpenOrCloseFile(fileID))
                                 \/ KnowSomeHandleOpenOnFile(fileID))
                            /\ MayUseBonaFideLease(fileID)
                            /\ ( \A mode \in req.modes:
                                    \/ ( /\ KnowNoHandleHasModeOnFile(mode,fileID)
                                         /\ KnowCanSetOrClearFileMode(fileID,mode))
                                    \/ KnowSomeHandleHasModeOnFile(mode,fileID))
                          THEN
                            \E newHandle \in Handle:
                               /\ HandleIsAvailable(newHandle)
                               /\ UNCHANGED ActiveProtectionRecords
                               /\ (FileValueTableState')=
                                  [
                                    [
                                      [
                                        [FileValueTableState EXCEPT
                                          ![fileID].openHandle.self[thisHost]=(@\union{newHandle})
                                        ]
                                      EXCEPT
                                        ![fileID].bonaFide[thisHost]=(@\union{newHandle})
                                      ]
                                    EXCEPT
                                      ![fileID]=
                                        [@EXCEPT
                                          !.modes=
                                            [mode \in DOMAIN@|->
                                              IF mode \in req.modes
                                              THEN
                                                LET
                                                  (*Defn*)AtSymbol001==@[mode]
                                                IN
                                                  [AtSymbol001 EXCEPT!.self[thisHost]=(@\union{newHandle})]
                                              ELSE
                                                @[mode]
                                            ]
                                        ]
                                    ]
                                  EXCEPT
                                    ![fileID]=
                                      [@EXCEPT
                                        !.accesses=
                                          [access \in DOMAIN@|->
                                            IF access \in reqAccesses
                                            THEN
                                              LET
                                                (*Defn*)AtSymbol002==@[access]
                                              IN
                                                [AtSymbol002 EXCEPT!.self[thisHost]=(@\union{newHandle})]
                                            ELSE
                                              @[access]
                                          ]
                                      ]
                                  ]
                               /\ UNCHANGED ActiveBorrowerRecords
                               /\ PostMessageInLog(
                                    MakeOpenFileOperationMessage(
                                      fileID,newHandle,KnowNoHandleOpenOnFile(fileID),req.modes,firstModes))
                               /\ ReturnSuccess(thread,newHandle)
                          ELSE
                            /\ NoReturn
                            /\ UNCHANGED ActiveBorrowerRecords
                            /\ NoChangeToMessageLog
                            /\ ( \E server \in Server:
                                    /\ ServerOwnsFile(server,fileID)
                                    /\ SendMessage(
                                         server,
                                         MakeOpenFileRequestMessage(
                                           fileID,
                                           MakeDistributedPriority(req.priority,thisHost),
                                           KnowNoHandleOpenOnFile(fileID),
                                           req.modes,
                                           firstModes)))

(* ********** Cleanup File ************************************************************************************************* *)

(*Defn*)PerformCleanupFileOperation==
  \E thread \in Thread,req \in Request:
     /\ IsRequestReady(thread,req)
     /\ req.cmd=CmdCleanup
     /\ IF req.handle \in RootHandle
        THEN
          ReturnArbitraryFailure(thread)
        ELSE IF
          \A fileID \in FileID:
             \/ KnowHandleNotOpenOnFile(req.handle,fileID)
             \/ KnowHandleOnFileNotBonaFide(req.handle,fileID)
        THEN
          ReturnArbitraryFailure(thread)
        ELSE
          \E fileID \in FileID:
             LET
               (*Defn*)handleModes==
                 {mode \in Mode:KnowHandleHasModeOnFile(req.handle,mode,fileID)}
               (*Defn*)lastModes==
                 {mode \in handleModes:KnowNoOtherHandleHasModeOnFile(req.handle,mode,fileID)}
             IN
               /\ KnowHandleOpenOnFile(req.handle,fileID)
               /\ KnowHandleOnFileIsBonaFide(req.handle,fileID)
               /\ IF
                    \A mode \in Mode:
                       \/ ( /\ KnowHandleHasModeOnFile(req.handle,mode,fileID)
                            /\ ( \/ ( /\ KnowNoOtherHandleHasModeOnFile(req.handle,mode,fileID)
                                      /\ KnowCanSetOrClearFileMode(fileID,mode))
                                 \/ KnowAnotherHandleHasModeOnFile(req.handle,mode,fileID)))
                       \/ KnowHandleLacksModeOnFile(req.handle,mode,fileID)
                  THEN
                    /\ UNCHANGED ActiveProtectionRecords
                    /\ (FileValueTableState')=
                       [
                         [FileValueTableState EXCEPT![fileID].bonaFide[thisHost]=(@\ {req.handle})]
                       EXCEPT
                         ![fileID]=
                           [@EXCEPT
                             !.modes=
                               [mode \in DOMAIN@|->
                                 IF mode \in Mode
                                 THEN
                                   LET
                                     (*Defn*)AtSymbol003==@[mode]
                                   IN
                                     [AtSymbol003 EXCEPT!.self[thisHost]=(@\ {req.handle})]
                                 ELSE
                                   @[mode]
                               ]
                           ]
                       ]
                    /\ UNCHANGED ActiveBorrowerRecords
                    /\ PostMessageInLog(
                         MakeCleanupFileOperationMessage(fileID,req.handle,handleModes,lastModes))
                    /\ ReturnSuccess(thread,Nil)
                  ELSE
                    /\ NoReturn
                    /\ UNCHANGED ActiveBorrowerRecords
                    /\ NoChangeToMessageLog
                    /\ ( \E server \in Server:
                            /\ ServerOwnsFile(server,fileID)
                            /\ SendMessage(
                                 server,
                                 MakeCleanupFileRequestMessage(
                                   fileID,MakeDistributedPriority(req.priority,thisHost),req.handle,lastModes)))

(* ********** Close File *************************************************************************************************** *)

(*Defn*)PerformCloseFileOperation==
  \E thread \in Thread,req \in Request:
     /\ IsRequestReady(thread,req)
     /\ req.cmd=CmdClose
     /\ IF req.handle \in RootHandle
        THEN
          ReturnArbitraryFailure(thread)
        ELSE IF
          \A fileID \in FileID:
             \/ KnowHandleNotOpenOnFile(req.handle,fileID)
             \/ KnowHandleOnFileIsBonaFide(req.handle,fileID)
        THEN
          ReturnArbitraryFailure(thread)
        ELSE
          \E fileID \in FileID:
             LET
               (*Defn*)unlinkPreclusion==
                 IF KnowAnotherHandleOpenOnFile(req.handle,fileID)
                 THEN
                   UPNotLastHandle
                 ELSE IF KnowFileNotDeletePending(fileID)
                 THEN
                   UPDelDispFalse
                 ELSE
                   UPOtherHandleOpen
             IN
               /\ KnowHandleOpenOnFile(req.handle,fileID)
               /\ KnowHandleOnFileNotBonaFide(req.handle,fileID)
               /\ IF
                    \/ ( /\ KnowNoOtherHandleOpenOnFile(req.handle,fileID)
                         /\ ( \/ KnowFileNotDeletePending(fileID)
                              \/ KnowFileOpenedByAnotherClient(fileID))
                         /\ KnowCanOpenOrCloseFile(fileID))
                    \/ KnowAnotherHandleOpenOnFile(req.handle,fileID)
                  THEN
                    /\ UNCHANGED ActiveProtectionRecords
                    /\ (FileValueTableState')=
                       [
                         [FileValueTableState EXCEPT
                           ![fileID].openHandle.self[thisHost]=(@\ {req.handle})
                         ]
                       EXCEPT
                         ![fileID]=
                           [@EXCEPT
                             !.accesses=
                               [access \in DOMAIN@|->
                                 IF access \in Access
                                 THEN
                                   LET
                                     (*Defn*)AtSymbol004==@[access]
                                   IN
                                     [AtSymbol004 EXCEPT![thisHost]=(@\ {req.handle})]
                                 ELSE
                                   @[access]
                               ]
                           ]
                       ]
                    /\ UNCHANGED ActiveBorrowerRecords
                    /\ PostMessageInLog(
                         MakeCloseFileOperationMessage(fileID,req.handle,unlinkPreclusion))
                    /\ ReturnSuccess(thread,Nil)
                  ELSE IF
                    /\ KnowNoOtherHandleOpenOnFile(req.handle,fileID)
                    /\ KnowFileNotOpenedByAnotherClient(fileID)
                    /\ KnowFileDeletePending(fileID)
                    /\ (\A rw \in PReadOrWrite:MayUseOpenHandleLease(fileID,BBSelf,rw))
                    /\ MayUseOpenHandleLease(fileID,BBOther,PRead)
                    /\ MayUseBonaFideLease(fileID)
                    /\ (\A mode \in Mode:MayUseModeLease(fileID,mode,BBSelf))
                    /\ (\A mode \in Mode:MayUseModeLease(fileID,mode,BBOther))
                    /\ (\A field \in FSharedValueFields:MayUseWriteSVLease(fileID,field))
                    /\ (\A label \in Label:MayUseWriteChildLease(fileID,label))
                    /\ ( \E parentFile \in FileID,label \in Label:
                            /\ KnowParentFile(fileID,label,parentFile)
                            /\ KnowChildFile(parentFile,label,fileID)
                            /\ MayUseWriteChildLease(parentFile,label))
                  THEN
                    \E parentFile \in FileID,label \in Label:
                       /\ KnowParentFile(fileID,label,parentFile)
                       /\ UpdateProtectionRecordsWithFileCloseAndUnlink(fileID)
                       /\ (FileValueTableState')=
                          [FileValueTableState EXCEPT
                            ![fileID]=FileValueInit,![parentFile].children[label]=Nil
                          ]
                       /\ UNCHANGED ActiveBorrowerRecords
                       /\ PostMessageSetInLog(
                            {
                            MakeCloseAndUnlinkFileOperationMessage(
                              CAUDChildFile,fileID,parentFile,req.handle,label),
                            MakeCloseAndUnlinkFileOperationMessage(
                              CAUDParentFile,fileID,parentFile,req.handle,label)
                            })
                       /\ ReturnSuccess(thread,Nil)
                  ELSE
                    /\ NoReturn
                    /\ UNCHANGED ActiveBorrowerRecords
                    /\ NoChangeToMessageLog
                    /\ IF
                         /\ KnowNoOtherHandleOpenOnFile(req.handle,fileID)
                         /\ KnowFileNotOpenedByAnotherClient(fileID)
                         /\ KnowFileDeletePending(fileID)
                       THEN
                         \/ ( /\ ( \/ (\E rw \in PReadOrWrite:(\neg MayUseOpenHandleLease(fileID,BBSelf,rw)))
                                   \/ (\neg MayUseOpenHandleLease(fileID,BBOther,PRead))
                                   \/ (\neg MayUseBonaFideLease(fileID))
                                   \/ (\E mode \in Mode:(\neg MayUseModeLease(fileID,mode,BBSelf)))
                                   \/ (\E mode \in Mode:(\neg MayUseModeLease(fileID,mode,BBOther)))
                                   \/ (\E field \in FSharedValueFields:(\neg MayUseWriteSVLease(fileID,field)))
                                   \/ (\E label \in Label:(\neg MayUseWriteChildLease(fileID,label))))
                              /\ ( \E server \in Server:
                                      /\ ServerOwnsFile(server,fileID)
                                      /\ SendMessage(
                                           server,
                                           MakeCloseFileRequestMessage(
                                             fileID,MakeDistributedPriority(req.priority,thisHost),req.handle))))
                         \/ ( \E parentFile \in FileID,label \in Label:
                                 /\ KnowParentFile(fileID,label,parentFile)
                                 /\ (\neg HaveWriteChildLease(parentFile,label))
                                 /\ ( \E server \in Server:
                                         /\ ServerOwnsFile(server,parentFile)
                                         /\ SendMessage(
                                              server,
                                              MakeUnlinkChildRequestMessage(
                                                parentFile,MakeDistributedPriority(req.priority,thisHost),label))))
                       ELSE
                         \E server \in Server:
                            /\ ServerOwnsFile(server,fileID)
                            /\ SendMessage(
                                 server,
                                 MakeCloseFileRequestMessage(
                                   fileID,MakeDistributedPriority(req.priority,thisHost),req.handle))

(* ********** Read File **************************************************************************************************** *)

(*Defn*)PerformReadFileOperation==
  \E thread \in Thread,req \in Request:
     /\ IsRequestReady(thread,req)
     /\ req.cmd=CmdRead
     /\ IF
          \A fileID \in FileID:
             \/ KnowHandleNotOpenOnFile(req.handle,fileID)
             \/ KnowHandleLacksAccessToFile(req.handle,ATReadable,fileID)
        THEN
          ReturnArbitraryFailure(thread)
        ELSE
          \E fileID \in FileID:
             /\ KnowHandleOpenOnFile(req.handle,fileID)
             /\ KnowHandleHasAccessToFile(req.handle,ATReadable,fileID)
             /\ IF MayUseReadOrWriteSVLease(fileID,FContent)
                THEN
                  /\ UNCHANGED ActiveProtectionRecords
                  /\ UNCHANGED FileValueTableState
                  /\ UNCHANGED ActiveBorrowerRecords
                  /\ NoChangeToMessageLog
                  /\ ReturnSuccess(thread,FileValueTableState[fileID].content)
                ELSE
                  /\ NoReturn
                  /\ UNCHANGED ActiveBorrowerRecords
                  /\ NoChangeToMessageLog
                  /\ ( \E server \in Server:
                          /\ ServerOwnsFile(server,fileID)
                          /\ SendMessage(
                               server,
                               MakeReadFileRequestMessage(
                                 fileID,MakeDistributedPriority(req.priority,thisHost))))

(* ********** Write File *************************************************************************************************** *)

(*Defn*)PerformWriteFileOperation==
  \E thread \in Thread,req \in Request:
     /\ IsRequestReady(thread,req)
     /\ req.cmd=CmdWrite
     /\ IF
          \A fileID \in FileID:
             \/ KnowHandleNotOpenOnFile(req.handle,fileID)
             \/ KnowHandleLacksAccessToFile(req.handle,ATWritable,fileID)
        THEN
          ReturnArbitraryFailure(thread)
        ELSE
          \E fileID \in FileID:
             /\ KnowHandleOpenOnFile(req.handle,fileID)
             /\ KnowHandleHasAccessToFile(req.handle,ATWritable,fileID)
             /\ IF MayUseWriteSVLease(fileID,FContent)
                THEN
                  /\ UNCHANGED ActiveProtectionRecords
                  /\ (FileValueTableState')=
                     [FileValueTableState EXCEPT![fileID].content=req.content]
                  /\ UNCHANGED ActiveBorrowerRecords
                  /\ PostMessageInLog(
                       MakeWriteFileOperationMessage(fileID,req.handle,req.content))
                  /\ ReturnSuccess(thread,Nil)
                ELSE
                  /\ NoReturn
                  /\ UNCHANGED ActiveBorrowerRecords
                  /\ NoChangeToMessageLog
                  /\ ( \E server \in Server:
                          /\ ServerOwnsFile(server,fileID)
                          /\ SendMessage(
                               server,
                               MakeWriteFileRequestMessage(
                                 fileID,MakeDistributedPriority(req.priority,thisHost))))

(* ********** Create File ************************************************************************************************** *)

(*Defn*)PerformCreateFileOperation==
  \E thread \in Thread,req \in Request:
     /\ IsRequestReady(thread,req)
     /\ req.cmd=CmdCreate
     /\ IF
          \A rootFile \in FileID:
             \/ KnowHandleNotOpenOnFile(req.handle,rootFile)
             \/ KnowHandleOnFileNotBonaFide(req.handle,rootFile)
        THEN
          ReturnArbitraryFailure(thread)
        ELSE IF req.path= <<>>
        THEN
          ReturnArbitraryFailure(thread)
        ELSE
          \E rootFile \in FileID:
             LET
               (*Defn*)pathPrefix==AllButLast(req.path)
               (*Defn*)createLabel==Last(req.path)
               (*Defn*)reqAccesses==ModeSetToAccessSet(req.modes)
               (*Defn*)sharedValueLeaseTime==EarlyClock+ClientShortLeaseTimeLimit
               (*Defn*)blackBoxReadSelfLeaseTime==EarlyClock+ClientLongLeaseTimeLimit
               (*Defn*)blackBoxWriteSelfLeaseTime==EarlyClock+ClientShortLeaseTimeLimit
               (*Defn*)blackBoxReadOtherLeaseTime==EarlyClock+ClientShortLeaseTimeLimit
               (*Defn*)privateValueLeaseTime==EarlyClock+ClientLongLeaseTimeLimit
             IN
               /\ KnowHandleOpenOnFile(req.handle,rootFile)
               /\ KnowHandleOnFileIsBonaFide(req.handle,rootFile)
               /\ IF KnowPathDoesNotResolve(rootFile,pathPrefix)
                  THEN
                    ReturnSpecificFailure(thread,RCErrorPathNotFound)
                  ELSE IF
                    \A parentFile \in FileID:
                       ( \neg KnowPathResolvesToTarget(rootFile,pathPrefix,parentFile))
                  THEN
                    /\ NoReturn
                    /\ ResolveNextPathStep(rootFile,pathPrefix,req.priority)
                  ELSE
                    \E parentFile \in FileID:
                       /\ KnowPathResolvesToTarget(rootFile,pathPrefix,parentFile)
                       /\ IF KnowLabelIsUsed(parentFile,createLabel)
                          THEN
                            ReturnSpecificFailure(thread,RCErrorFileAlreadyExists)
                          ELSE IF KnowFileDeletePending(parentFile)
                          THEN
                            ReturnArbitraryFailure(thread)
                          ELSE IF
                            /\ KnowLabelIsUnused(parentFile,createLabel)
                            /\ KnowFileNotDeletePending(parentFile)
                            /\ MayUseWriteChildLease(parentFile,createLabel)
                            /\ IchildOfFileHasBeenBorrowed(parentFile)
                          THEN
                            \E newHandle \in Handle,newFile \in FileID,maxSuffix \in FileIDComponent:
                               /\ HandleIsAvailable(newHandle)
                               /\ RetrieveBorrowedFileAndBorrowIchildren(parentFile,newFile,maxSuffix)
                               /\ UpdateProtectionRecordsWithFileCreate(
                                    newFile,
                                    sharedValueLeaseTime,
                                    blackBoxReadSelfLeaseTime,
                                    blackBoxWriteSelfLeaseTime,
                                    blackBoxReadOtherLeaseTime,
                                    privateValueLeaseTime)
                               /\ (FileValueTableState')=
                                  [FileValueTableState EXCEPT
                                    ![parentFile].children[createLabel]=newFile,
                                    ![newFile]=
                                      [
                                        [
                                          [
                                            [[FileValueInit EXCEPT!.parent=MakeParent(parentFile,createLabel)]EXCEPT
                                              !.openHandle.self[thisHost]={newHandle}
                                            ]
                                          EXCEPT
                                            !.bonaFide[thisHost]={newHandle}
                                          ]
                                        EXCEPT
                                          !.modes=
                                            [mode \in DOMAIN@|->
                                              IF mode \in req.modes
                                              THEN
                                                LET
                                                  (*Defn*)AtSymbol005==@[mode]
                                                IN
                                                  [AtSymbol005 EXCEPT!.self[thisHost]={newHandle}]
                                              ELSE
                                                @[mode]
                                            ]
                                        ]
                                      EXCEPT
                                        !.accesses=
                                          [access \in DOMAIN@|->
                                            IF access \in reqAccesses
                                            THEN
                                              LET
                                                (*Defn*)AtSymbol006==@[access]
                                              IN
                                                [AtSymbol006 EXCEPT![thisHost]={newHandle}]
                                            ELSE
                                              @[access]
                                          ]
                                      ]
                                  ]
                               /\ PostMessageInLog(
                                    MakeCreateFileOperationMessage(
                                      newFile,
                                      parentFile,
                                      createLabel,
                                      newHandle,
                                      req.modes,
                                      sharedValueLeaseTime,
                                      blackBoxReadSelfLeaseTime,
                                      blackBoxWriteSelfLeaseTime,
                                      blackBoxReadOtherLeaseTime,
                                      privateValueLeaseTime,
                                      maxSuffix))
                               /\ ReturnSuccess(thread,newHandle)
                          ELSE
                            /\ NoReturn
                            /\ ( \/ ( /\ (\neg IchildOfFileHasBeenBorrowed(parentFile))
                                      /\ IF KnowFileCreationInProgress(parentFile)
                                         THEN
                                           /\ LocallyBorrowIchild(parentFile)
                                           /\ SendNoMessage
                                         ELSE
                                           \E server \in Server:
                                              /\ ServerOwnsFile(server,parentFile)
                                              /\ UNCHANGED ActiveBorrowerRecords
                                              /\ NoChangeToMessageLog
                                              /\ SendMessage(server,MakeFileOwnershipLoanRequestMessage(parentFile)))
                                 \/ ( /\ ( \/ (\neg KnowFileNotDeletePending(parentFile))
                                           \/ (\neg HaveWriteChildLease(parentFile,createLabel)))
                                      /\ UNCHANGED ActiveBorrowerRecords
                                      /\ NoChangeToMessageLog
                                      /\ ( \E server \in Server:
                                              /\ ServerOwnsFile(server,parentFile)
                                              /\ SendMessage(
                                                   server,
                                                   MakeCreateFileRequestMessage(
                                                     parentFile,MakeDistributedPriority(req.priority,thisHost),createLabel)))))

(* ********** OpenOrCreate File ******************************************************************************************** *)

(*Defn*)PerformOpenOrCreateFileOperation==
  \E thread \in Thread,req \in Request:
     /\ IsRequestReady(thread,req)
     /\ req.cmd=CmdOpenOrCreate
     /\ IF
          \A rootFile \in FileID:
             \/ KnowHandleNotOpenOnFile(req.handle,rootFile)
             \/ KnowHandleOnFileNotBonaFide(req.handle,rootFile)
        THEN
          ReturnArbitraryFailure(thread)
        ELSE IF req.path= <<>>
        THEN
          ReturnArbitraryFailure(thread)
        ELSE
          \E rootFile \in FileID:
             /\ KnowHandleOpenOnFile(req.handle,rootFile)
             /\ KnowHandleOnFileIsBonaFide(req.handle,rootFile)
             /\ IF KnowPathDoesNotResolve(rootFile,AllButLast(req.path))
                THEN
                  ReturnArbitraryFailure(thread)
                ELSE IF
                  /\ (\neg KnowPathDoesNotResolve(rootFile,req.path))
                  /\ ( \A fileID \in FileID:(\neg KnowPathResolvesToTarget(rootFile,req.path,fileID)))
                THEN
                  /\ NoReturn
                  /\ ResolveNextPathStep(rootFile,req.path,req.priority)
                ELSE IF KnowPathDoesNotResolve(rootFile,req.path)
                THEN
                  \E parentFile \in FileID:
                     LET
                       (*Defn*)pathPrefix==AllButLast(req.path)
                       (*Defn*)createLabel==Last(req.path)
                       (*Defn*)reqAccesses==ModeSetToAccessSet(req.modes)
                       (*Defn*)sharedValueLeaseTime==EarlyClock+ClientShortLeaseTimeLimit
                       (*Defn*)blackBoxReadSelfLeaseTime==EarlyClock+ClientLongLeaseTimeLimit
                       (*Defn*)blackBoxWriteSelfLeaseTime==EarlyClock+ClientShortLeaseTimeLimit
                       (*Defn*)blackBoxReadOtherLeaseTime==EarlyClock+ClientShortLeaseTimeLimit
                       (*Defn*)privateValueLeaseTime==EarlyClock+ClientLongLeaseTimeLimit
                     IN
                       /\ KnowPathResolvesToTarget(rootFile,pathPrefix,parentFile)
                       /\ IF KnowLabelIsUsed(parentFile,createLabel)
                          THEN
                            ReturnSpecificFailure(thread,RCErrorFileAlreadyExists)
                          ELSE IF KnowFileDeletePending(parentFile)
                          THEN
                            ReturnArbitraryFailure(thread)
                          ELSE IF
                            /\ KnowLabelIsUnused(parentFile,createLabel)
                            /\ KnowFileNotDeletePending(parentFile)
                            /\ MayUseWriteChildLease(parentFile,createLabel)
                            /\ IchildOfFileHasBeenBorrowed(parentFile)
                          THEN
                            \E newHandle \in Handle,newFile \in FileID,maxSuffix \in FileIDComponent:
                               /\ HandleIsAvailable(newHandle)
                               /\ RetrieveBorrowedFileAndBorrowIchildren(parentFile,newFile,maxSuffix)
                               /\ UpdateProtectionRecordsWithFileCreate(
                                    newFile,
                                    sharedValueLeaseTime,
                                    blackBoxReadSelfLeaseTime,
                                    blackBoxWriteSelfLeaseTime,
                                    blackBoxReadOtherLeaseTime,
                                    privateValueLeaseTime)
                               /\ (FileValueTableState')=
                                  [FileValueTableState EXCEPT
                                    ![parentFile].children[createLabel]=newFile,
                                    ![newFile]=
                                      [
                                        [
                                          [
                                            [[FileValueInit EXCEPT!.parent=MakeParent(parentFile,createLabel)]EXCEPT
                                              !.openHandle.self[thisHost]={newHandle}
                                            ]
                                          EXCEPT
                                            !.bonaFide[thisHost]={newHandle}
                                          ]
                                        EXCEPT
                                          !.modes=
                                            [mode \in DOMAIN@|->
                                              IF mode \in req.modes
                                              THEN
                                                LET
                                                  (*Defn*)AtSymbol007==@[mode]
                                                IN
                                                  [AtSymbol007 EXCEPT!.self[thisHost]={newHandle}]
                                              ELSE
                                                @[mode]
                                            ]
                                        ]
                                      EXCEPT
                                        !.accesses=
                                          [access \in DOMAIN@|->
                                            IF access \in reqAccesses
                                            THEN
                                              LET
                                                (*Defn*)AtSymbol008==@[access]
                                              IN
                                                [AtSymbol008 EXCEPT![thisHost]={newHandle}]
                                            ELSE
                                              @[access]
                                          ]
                                      ]
                                  ]
                               /\ PostMessageInLog(
                                    MakeCreateFileOperationMessage(
                                      newFile,
                                      parentFile,
                                      createLabel,
                                      newHandle,
                                      req.modes,
                                      sharedValueLeaseTime,
                                      blackBoxReadSelfLeaseTime,
                                      blackBoxWriteSelfLeaseTime,
                                      blackBoxReadOtherLeaseTime,
                                      privateValueLeaseTime,
                                      maxSuffix))
                               /\ ReturnSuccess(thread,newHandle)
                          ELSE
                            /\ NoReturn
                            /\ ( \/ ( /\ (\neg IchildOfFileHasBeenBorrowed(parentFile))
                                      /\ IF KnowFileCreationInProgress(parentFile)
                                         THEN
                                           /\ LocallyBorrowIchild(parentFile)
                                           /\ SendNoMessage
                                         ELSE
                                           \E server \in Server:
                                              /\ ServerOwnsFile(server,parentFile)
                                              /\ UNCHANGED ActiveBorrowerRecords
                                              /\ NoChangeToMessageLog
                                              /\ SendMessage(server,MakeFileOwnershipLoanRequestMessage(parentFile)))
                                 \/ ( /\ ( \/ (\neg KnowFileNotDeletePending(parentFile))
                                           \/ (\neg HaveWriteChildLease(parentFile,createLabel)))
                                      /\ UNCHANGED ActiveBorrowerRecords
                                      /\ NoChangeToMessageLog
                                      /\ ( \E server \in Server:
                                              /\ ServerOwnsFile(server,parentFile)
                                              /\ SendMessage(
                                                   server,
                                                   MakeCreateFileRequestMessage(
                                                     parentFile,MakeDistributedPriority(req.priority,thisHost),createLabel)))))
                ELSE
                  \E fileID \in FileID:
                     LET
                       (*Defn*)firstModes==
                         {mode \in req.modes:KnowNoHandleHasModeOnFile(mode,fileID)}
                       (*Defn*)reqAccesses==ModeSetToAccessSet(req.modes)
                     IN
                       /\ KnowPathResolvesToTarget(rootFile,req.path,fileID)
                       /\ IF KnowModeSetConflicts(fileID,req.modes)
                          THEN
                            ReturnArbitraryFailure(thread)
                          ELSE IF KnowFileDeletePending(fileID)
                          THEN
                            ReturnArbitraryFailure(thread)
                          ELSE IF
                            /\ KnowModeSetCompatible(fileID,req.modes)
                            /\ KnowFileNotDeletePending(fileID)
                            /\ ( \/ ( /\ KnowNoHandleOpenOnFile(fileID)
                                      /\ KnowCanOpenOrCloseFile(fileID))
                                 \/ KnowSomeHandleOpenOnFile(fileID))
                            /\ MayUseBonaFideLease(fileID)
                            /\ ( \A mode \in req.modes:
                                    \/ ( /\ KnowNoHandleHasModeOnFile(mode,fileID)
                                         /\ KnowCanSetOrClearFileMode(fileID,mode))
                                    \/ KnowSomeHandleHasModeOnFile(mode,fileID))
                          THEN
                            \E newHandle \in Handle:
                               /\ HandleIsAvailable(newHandle)
                               /\ UNCHANGED ActiveProtectionRecords
                               /\ (FileValueTableState')=
                                  [
                                    [
                                      [
                                        [FileValueTableState EXCEPT
                                          ![fileID].openHandle.self[thisHost]=(@\union{newHandle})
                                        ]
                                      EXCEPT
                                        ![fileID].bonaFide[thisHost]=(@\union{newHandle})
                                      ]
                                    EXCEPT
                                      ![fileID]=
                                        [@EXCEPT
                                          !.modes=
                                            [mode \in DOMAIN@|->
                                              IF mode \in req.modes
                                              THEN
                                                LET
                                                  (*Defn*)AtSymbol009==@[mode]
                                                IN
                                                  [AtSymbol009 EXCEPT!.self[thisHost]=(@\union{newHandle})]
                                              ELSE
                                                @[mode]
                                            ]
                                        ]
                                    ]
                                  EXCEPT
                                    ![fileID]=
                                      [@EXCEPT
                                        !.accesses=
                                          [access \in DOMAIN@|->
                                            IF access \in reqAccesses
                                            THEN
                                              LET
                                                (*Defn*)AtSymbol010==@[access]
                                              IN
                                                [AtSymbol010 EXCEPT!.self[thisHost]=(@\union{newHandle})]
                                            ELSE
                                              @[access]
                                          ]
                                      ]
                                  ]
                               /\ UNCHANGED ActiveBorrowerRecords
                               /\ PostMessageInLog(
                                    MakeOpenFileOperationMessage(
                                      fileID,newHandle,KnowNoHandleOpenOnFile(fileID),req.modes,firstModes))
                               /\ ReturnSuccess(thread,newHandle)
                          ELSE
                            /\ NoReturn
                            /\ UNCHANGED ActiveBorrowerRecords
                            /\ NoChangeToMessageLog
                            /\ ( \E server \in Server:
                                    /\ ServerOwnsFile(server,fileID)
                                    /\ SendMessage(
                                         server,
                                         MakeOpenFileRequestMessage(
                                           fileID,
                                           MakeDistributedPriority(req.priority,thisHost),
                                           KnowNoHandleOpenOnFile(fileID),
                                           req.modes,
                                           firstModes)))

(* ********** Delete File ************************************************************************************************** *)

(*Defn*)PerformDeleteFileOperation==
  \E thread \in Thread,req \in Request:
     /\ IsRequestReady(thread,req)
     /\ req.cmd=CmdDelete
     /\ IF
          \A fileID \in FileID:
             \/ KnowHandleNotOpenOnFile(req.handle,fileID)
             \/ KnowHandleLacksModeOnFile(req.handle,MTAccessDelete,fileID)
             \/ KnowHandleOnFileNotBonaFide(req.handle,fileID)
        THEN
          ReturnArbitraryFailure(thread)
        ELSE
          \E fileID \in FileID:
             /\ KnowHandleOpenOnFile(req.handle,fileID)
             /\ KnowHandleHasModeOnFile(req.handle,MTAccessDelete,fileID)
             /\ KnowHandleOnFileIsBonaFide(req.handle,fileID)
             /\ IF
                  /\ req.delDisp
                  /\ KnowFileHasChildren(fileID)
                THEN
                  ReturnArbitraryFailure(thread)
                ELSE IF
                  /\ MayUseReadOrWriteSVLease(fileID,FDelDisp)
                  /\ FileValueTableState[fileID].delDisp=req.delDisp
                THEN
                  /\ UNCHANGED FileValueTableState
                  /\ UNCHANGED ActiveProtectionRecords
                  /\ UNCHANGED ActiveBorrowerRecords
                  /\ NoChangeToMessageLog
                  /\ ReturnSuccess(thread,Nil)
                ELSE IF
                  /\ MayUseWriteSVLease(fileID,FDelDisp)
                  /\ (req.delDisp=>KnowFileHasNoChildren(fileID))
                THEN
                  /\ UNCHANGED ActiveProtectionRecords
                  /\ UNCHANGED ActiveBorrowerRecords
                  /\ (FileValueTableState')=
                     [FileValueTableState EXCEPT![fileID].delDisp=req.delDisp]
                  /\ PostMessageInLog(
                       MakeDeleteFileOperationMessage(fileID,req.handle,req.delDisp))
                  /\ ReturnSuccess(thread,Nil)
                ELSE
                  /\ NoReturn
                  /\ UNCHANGED ActiveBorrowerRecords
                  /\ NoChangeToMessageLog
                  /\ ( \E server \in Server:
                          /\ ServerOwnsFile(server,fileID)
                          /\ SendMessage(
                               server,
                               MakeDeleteFileRequestMessage(
                                 fileID,MakeDistributedPriority(req.priority,thisHost),req.delDisp)))

(* ********** Move File **************************************************************************************************** *)

(*Defn*)PerformMoveFileOperation==
  \E thread \in Thread,req \in Request:
     /\ IsRequestReady(thread,req)
     /\ req.cmd=CmdMove
     /\ IF
          \/ ( \A childFile \in FileID:
                  \/ KnowHandleNotOpenOnFile(req.childHandle,childFile)
                  \/ KnowHandleOnFileNotBonaFide(req.childHandle,childFile))
          \/ ( \A destRootFile \in FileID:
                  \/ KnowHandleNotOpenOnFile(req.destRootHandle,destRootFile)
                  \/ KnowHandleOnFileNotBonaFide(req.destRootHandle,destRootFile))
        THEN
          ReturnArbitraryFailure(thread)
        ELSE
          \E childFile \in FileID,destRootFile \in FileID:
             LET
               (*Defn*)destPathPrefix==AllButLast(req.destPath)
               (*Defn*)destLabel==Last(req.destPath)
             IN
               /\ KnowHandleOpenOnFile(req.childHandle,childFile)
               /\ KnowHandleOnFileIsBonaFide(req.childHandle,childFile)
               /\ KnowHandleOpenOnFile(req.destRootHandle,destRootFile)
               /\ KnowHandleOnFileIsBonaFide(req.destRootHandle,destRootFile)
               /\ IF req.destPath= <<>>
                  THEN
                    ReturnArbitraryFailure(thread)
                  ELSE IF KnowPathDoesNotResolve(destRootFile,destPathPrefix)
                  THEN
                    ReturnArbitraryFailure(thread)
                  ELSE IF
                    \A destParentFile \in FileID:
                       ( \neg KnowPathResolvesToTarget(destRootFile,destPathPrefix,destParentFile))
                  THEN
                    /\ NoReturn
                    /\ ResolveNextPathStep(destRootFile,destPathPrefix,req.priority)
                  ELSE
                    \E destParentFile \in FileID:
                       /\ KnowPathResolvesToTarget(destRootFile,destPathPrefix,destParentFile)
                       /\ IF KnowLabelIsUsed(destParentFile,destLabel)
                          THEN
                            ReturnArbitraryFailure(thread)
                          ELSE IF KnowFileDeletePending(destParentFile)
                          THEN
                            ReturnArbitraryFailure(thread)
                          ELSE IF
                            \E destPartialFilePath \in FileSeq:
                               /\ KnowFileHasPartialFilePath(destParentFile,destPartialFilePath)
                               /\ IsElementInSeq(childFile,destPartialFilePath)
                          THEN
                            ReturnArbitraryFailure(thread)
                          ELSE IF
                            /\ ( \E destFullFilePath \in FileSeq:
                                    /\ KnowFileHasFullFilePath(destParentFile,destFullFilePath)
                                    /\ KnowFileHasWarrantiedAncestorPath(
                                         destParentFile,AllButLast(destFullFilePath))
                                    /\ (\neg IsElementInSeq(childFile,destFullFilePath)))
                            /\ KnowLabelIsUnused(destParentFile,destLabel)
                            /\ KnowFileNotDeletePending(destParentFile)
                            /\ MayUseWriteChildLease(destParentFile,destLabel)
                            /\ MayUseWriteSVLease(childFile,FParent)
                            /\ ( \E srcParentFile \in FileID,srcLabel \in Label:
                                    /\ KnowParentFile(childFile,srcLabel,srcParentFile)
                                    /\ KnowChildFile(srcParentFile,srcLabel,childFile)
                                    /\ MayUseWriteChildLease(srcParentFile,srcLabel))
                          THEN
                            \E srcParentFile \in FileID,srcLabel \in Label:
                               /\ KnowParentFile(childFile,srcLabel,srcParentFile)
                               /\ UNCHANGED ActiveProtectionRecords
                               /\ (FileValueTableState')=
                                  [FileValueTableState EXCEPT
                                    ![srcParentFile].children[srcLabel]=Nil,
                                    ![destParentFile].children[destLabel]=childFile,
                                    ![childFile].parent=MakeParent(destParentFile,destLabel)
                                  ]
                               /\ UNCHANGED ActiveBorrowerRecords
                               /\ PostMessageSetInLog(
                                    {
                                    MakeMoveFileOperationMessage(
                                      MDChildFile,
                                      childFile,
                                      req.childHandle,
                                      srcParentFile,
                                      srcLabel,
                                      destParentFile,
                                      destLabel),
                                    MakeMoveFileOperationMessage(
                                      MDSrcParentFile,
                                      childFile,
                                      req.childHandle,
                                      srcParentFile,
                                      srcLabel,
                                      destParentFile,
                                      destLabel),
                                    MakeMoveFileOperationMessage(
                                      MDDestParentFile,
                                      childFile,
                                      req.childHandle,
                                      srcParentFile,
                                      srcLabel,
                                      destParentFile,
                                      destLabel)
                                    })
                               /\ ReturnSuccess(thread,Nil)
                          ELSE
                            /\ NoReturn
                            /\ ( \/ ( /\ ( \A destFullFilePath \in FileSeq:
                                              ( \neg KnowFileHasFullFilePath(destParentFile,destFullFilePath)))
                                      /\ ResolvePreviousPathStep(destParentFile,req.priority))
                                 \/ ( \E server \in Server:
                                         /\ ( \/ (\neg KnowFileNotDeletePending(destParentFile))
                                              \/ (\neg HaveWriteChildLease(destParentFile,destLabel))
                                              \/ ( \A destFullFilePath \in FileSeq:
                                                      ( \neg
                                                        KnowFileHasWarrantiedAncestorPath(
                                                          destParentFile,AllButLast(destFullFilePath)))))
                                         /\ ServerOwnsFile(server,destParentFile)
                                         /\ UNCHANGED ActiveBorrowerRecords
                                         /\ NoChangeToMessageLog
                                         /\ SendMessage(
                                              server,
                                              MakeLinkChildRequestMessage(
                                                destParentFile,MakeDistributedPriority(req.priority,thisHost),destLabel)))
                                 \/ ( \E server \in Server:
                                         /\ (\neg HaveWriteSVLease(childFile,FParent))
                                         /\ ServerOwnsFile(server,childFile)
                                         /\ UNCHANGED ActiveBorrowerRecords
                                         /\ NoChangeToMessageLog
                                         /\ SendMessage(
                                              server,
                                              MakeMoveFileRequestMessage(
                                                childFile,MakeDistributedPriority(req.priority,thisHost))))
                                 \/ ( \E srcParentFile \in FileID,srcLabel \in Label,server \in Server:
                                         /\ KnowParentFile(childFile,srcLabel,srcParentFile)
                                         /\ (\neg HaveWriteChildLease(srcParentFile,srcLabel))
                                         /\ ServerOwnsFile(server,srcParentFile)
                                         /\ UNCHANGED ActiveBorrowerRecords
                                         /\ NoChangeToMessageLog
                                         /\ SendMessage(
                                              server,
                                              MakeUnlinkChildRequestMessage(
                                                srcParentFile,MakeDistributedPriority(req.priority,thisHost),srcLabel))))
====
