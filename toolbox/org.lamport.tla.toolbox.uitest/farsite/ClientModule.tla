---- MODULE ClientModule ----
(*`^\addcontentsline{toc}{section}{ClientModule}^'*)

EXTENDS
  ClientOperationProcessorModule,ClientLeaseManagerModule,ClientFaultModule
(* ClientFault actions *)

(*Defn*)ExerciseByzantineFault==
  /\ ReceiveNoMessage
  /\ NoChangeToMessageLog
  /\ NoChangeToLeaseRecallMessageBuffer
  /\ NoChangeToFileOwnership
  /\ UNCHANGED FileValueTableState
  /\ UNCHANGED ActiveProtectionRecords
  /\ UNCHANGED ThreadTable
  /\ ( \/ CorruptThisClient
       \/ SendArbitraryMessage
       \/ SignArbitraryCertificate)

(* ClientFileOwnership actions *)

(*Defn*)ProcessFileOwnershipMessage==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ SendNoMessage
  /\ NoChangeToMessageLog
  /\ NoChangeToLeaseRecallMessageBuffer
  /\ UNCHANGED FileValueTableState
  /\ UNCHANGED ActiveProtectionRecords
  /\ UNCHANGED ThreadTable
  /\ ( \/ ProcessFileOwnershipNotificationMessage
       \/ ProcessFileOwnershipLoanGrantMessage)

(* ClientFileProtection actions *)

(*Defn*)ManageProtectionRecords==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ SendNoMessage
  /\ ReceiveNoMessage
  /\ NoChangeToMessageLog
  /\ NoChangeToLeaseRecallMessageBuffer
  /\ NoChangeToFileOwnership
  /\ UNCHANGED FileValueTableState
  /\ UNCHANGED ThreadTable
  /\ DiscardDefunctProtectionRecord

(* ClientLeaseManager actions *)

(*Defn*)ManageLeases==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ NoChangeToFileOwnership
  /\ UNCHANGED ThreadTable
  /\ ( \/ ProcessSingletonLeaseRecallMessage
       \/ ProcessInfiniteChildLeaseRecallMessage
       \/ ProcessSingletonLeaseGrantMessage
       \/ ProcessInfiniteChildLeaseGrantMessage
       \/ ProcessSingletonLeaseGrantCertificateMessage
       \/ RequestLeaseExtension
       \/ ProactivelyReleaseLease
       \/ RecoverOpenHandleReadSelfLease
       \/ RecoverBonaFideLease)

(* ClientLog actions *)

(*Defn*)ManageOperationLog==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ NoChangeToLeaseRecallMessageBuffer
  /\ NoChangeToFileOwnership
  /\ UNCHANGED ThreadTable
  /\ ( \/ SendBatchUpdateFromLog
       \/ ProcessPositiveAcknowledgementMessage
       \/ ProcessNegativeAcknowledgementMessage
       \/ DiscardOperationMessagesFromLog
       \/ DiscardLeaseReleaseMessageFromLog)

(* ClientMessageBuffer actions *)

(*Defn*)ManageLeaseRecallMessageBuffer==
  /\ NoChangeToCorruption
  /\ SendNoMessage
  /\ SignNoCertificate
  /\ NoChangeToFileOwnership
  /\ UNCHANGED ThreadTable
  /\ UNCHANGED FileValueTableState
  /\ UNCHANGED ActiveProtectionRecords
  /\ NoChangeToMessageLog
  /\ BufferLeaseRecallMessage

(* ClientOperationProcessor actions *)

(*Defn*)PerformRequestedFileOperation==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ ReceiveNoMessage
  /\ NoChangeToLeaseRecallMessageBuffer
  /\ ( \/ PerformOpenFileOperation
       \/ PerformCleanupFileOperation
       \/ PerformCloseFileOperation
       \/ PerformReadFileOperation
       \/ PerformWriteFileOperation
       \/ PerformCreateFileOperation
       \/ PerformOpenOrCreateFileOperation
       \/ PerformDeleteFileOperation
       \/ PerformMoveFileOperation)

(* Thread actions *)

(*Defn*)ReceiveApplicationRequest==
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ SendNoMessage
  /\ ReceiveNoMessage
  /\ NoChangeToFileOwnership
  /\ NoChangeToMessageLog
  /\ NoChangeToLeaseRecallMessageBuffer
  /\ UNCHANGED FileValueTableState
  /\ UNCHANGED ActiveProtectionRecords
  /\ ReceiveOperationRequest

(*Defn*)Init==
  /\ ActionSerialNumber=ActionSerialNumberInit
  /\ Corrupted=CorruptedInit
  /\ FileMap=FileMapInit
  /\ ActiveBorrowerRecords=ActiveBorrowerRecordsInit
  /\ MessageLog=MessageLogInit
  /\ LeaseRecallMessageBuffer=LeaseRecallMessageBufferInit
  /\ ThreadTable=ThreadTableInit
  /\ FileValueTableState=FileValueTableInit
  /\ ActiveProtectionRecords=ActiveProtectionRecordsInit

(*Defn*)Next==
  /\ AdvanceActionSerialNumber
  /\ ( \/ ExerciseByzantineFault
       \/ ProcessFileOwnershipMessage
       \/ ManageProtectionRecords
       \/ ManageLeases
       \/ ManageOperationLog
       \/ ManageLeaseRecallMessageBuffer
       \/ PerformRequestedFileOperation
       \/ ReceiveApplicationRequest)

(*Defn*)DoNothing==
  /\ UNCHANGED ActionSerialNumber
  /\ NoChangeToCorruption
  /\ SignNoCertificate
  /\ SendNoMessage
  /\ ReceiveNoMessage
  /\ NoChangeToMessageLog
  /\ NoChangeToFileOwnership
  /\ UNCHANGED FileValueTableState
  /\ UNCHANGED ActiveProtectionRecords
  /\ UNCHANGED ThreadTable
====
