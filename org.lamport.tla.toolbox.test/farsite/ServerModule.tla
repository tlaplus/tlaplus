---- MODULE ServerModule ----
(*`^\addcontentsline{toc}{section}{ServerModule}^'*)

EXTENDS
  ServerOperationProcessorModule,
  ServerLeaseManagerModule,
  ServerPhantomClientModule,
  ServerFaultModule
(* ServerFault actions *)

(*Defn*)ExerciseByzantineFault==
  /\ ReceiveNoMessage
  /\ NoChangeToFileOwnership
  /\ NoChangeToConsistencyMessageBuffer
  /\ NoChangeToLeaseRequestMessageBuffer
  /\ NoChangeToInterlockMessageBuffer
  /\ UNCHANGED FileValueTableState
  /\ UNCHANGED FileProtectionTableState
  /\ NoChangeToServerExistence
  /\ ( \/ CorruptThisServer
       \/ SendArbitraryMessage
       \/ SignArbitraryCertificate)

(* ServerFileOwnership actions, except for CompleteDelegationOfFileOwnership *)

(*Defn*)ManageFileOwnership==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ NoChangeToConsistencyMessageBuffer
  /\ NoChangeToLeaseRequestMessageBuffer
  /\ NoChangeToInterlockMessageBuffer
  /\ ( \/ ProcessFileOwnershipNotificationMessage
       \/ ProcessFileOwnershipLoanRequestMessage
       \/ ProcessFileOwnershipQueryMessage
       \/ InitiateDelegationOfFileOwnership)

(* ServerFileOwnership action CompleteDelegationOfFileOwnership *)

(*Defn*)ComeIntoExistence==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ NoChangeToConsistencyMessageBuffer
  /\ NoChangeToLeaseRequestMessageBuffer
  /\ NoChangeToInterlockMessageBuffer
  /\ CompleteDelegationOfFileOwnership

(* ServerLeaseManager actions *)

(*Defn*)ManageLeases==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ ReceiveNoMessage
  /\ NoChangeToFileOwnership
  /\ NoChangeToServerExistence
  /\ ( \/ ProcessOpenFileRequestMessage
       \/ ProcessCleanupFileRequestMessage
       \/ ProcessCloseFileRequestMessage
       \/ ProcessReadFileRequestMessage
       \/ ProcessWriteFileRequestMessage
       \/ ProcessDeleteFileRequestMessage
       \/ ProcessUnlinkChildRequestMessage
       \/ ProcessLinkChildRequestMessage
       \/ ProcessResolveLabelRequestMessage
       \/ ProcessIdentifyParentRequestMessage
       \/ ProcessLeaseExtensionRequestMessage
       \/ ProcessOpenHandleReadSelfRequestMessage
       \/ ProcessBonaFideRequestMessage
       \/ ProcessPathRequestMessage
       \/ ProcessPathGrantMessage
       \/ ProcessPathRecallMessage
       \/ ProcessPathReleaseMessage
       \/ ProcessLeaseReleaseMessage)

(* ServerMessageBuffer actions *)

(*Defn*)ManageMessageBuffers==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ UNCHANGED FileValueTableState
  /\ UNCHANGED FileProtectionTableState
  /\ NoChangeToFileOwnership
  /\ NoChangeToServerExistence
  /\ ( \/ BufferBatchUpdateMessage
       \/ DiscardMessagesFromConsistencyBuffer
       \/ BufferLeaseRequestMessage
       \/ RejectMessagesFromLeaseRequestBuffer
       \/ DiscardMessagesFromLeaseRequestBuffer
       \/ BufferServerInterlockMessage
       \/ ManageMessageInInterlockBuffer)

(* ServerOperationProcessor actions *)

(*Defn*)ProcessOperationMessage==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ ReceiveNoMessage
  /\ NoChangeToLeaseRequestMessageBuffer
  /\ NoChangeToServerExistence
  /\ ( \/ ProcessOpenFileOperation
       \/ ProcessCleanupFileOperation
       \/ ProcessCloseFileOperation
       \/ ProcessCloseAndUnlinkFileOperation
       \/ ProcessWriteFileOperation
       \/ ProcessCreateFileOperation
       \/ ProcessDeleteFileOperation
       \/ ProcessMoveFileOperation)

(* ServerPhantomClient actions *)

(*Defn*)PerformPhantomClientOperation==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ ReceiveNoMessage
  /\ NoChangeToConsistencyMessageBuffer
  /\ NoChangeToLeaseRequestMessageBuffer
  /\ NoChangeToFileOwnership
  /\ NoChangeToServerExistence
  /\ ( \/ PerformPhantomCleanupFile
       \/ ChildPerformOrPreparePhantomCloseFile
       \/ ChildCommitPhantomCloseAndUnlinkFile
       \/ ParentProcessPhantomCloseAndUnlinkFile)

(*Defn*)Init==
  /\ Corrupted=CorruptedInit
  /\ OwnershipAuthorizingServer=OwnershipAuthorizingServerInit
  /\ IssuedDeeds=IssuedDeedsInit
  /\ FileMap=FileMapInit
  /\ ActiveBorrowerRecords=ActiveBorrowerRecordsInit
  /\ ConsistencyMessageBuffer=ConsistencyMessageBufferInit
  /\ LeaseRequestMessageBuffer=LeaseRequestMessageBufferInit
  /\ InterlockMessageBuffer=InterlockMessageBufferInit
  /\ FileValueTableState=FileValueTableInit
  /\ FileProtectionTableState=FileProtectionTableInit

(*Defn*)Next==
  \/ ExerciseByzantineFault
  \/ ManageFileOwnership
  \/ ManageLeases
  \/ ManageMessageBuffers
  \/ ProcessOperationMessage
  \/ PerformPhantomClientOperation

(*Defn*)DoNothing==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ SendNoMessage
  /\ ReceiveNoMessage
  /\ NoChangeToFileOwnership
  /\ NoChangeToConsistencyMessageBuffer
  /\ NoChangeToLeaseRequestMessageBuffer
  /\ NoChangeToInterlockMessageBuffer
  /\ UNCHANGED FileValueTableState
  /\ UNCHANGED FileProtectionTableState
  /\ NoChangeToServerExistence
====
