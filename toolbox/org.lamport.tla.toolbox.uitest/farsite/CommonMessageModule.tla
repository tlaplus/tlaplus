---- MODULE CommonMessageModule ----
(*`^\addcontentsline{toc}{section}{CommonMessageModule}^'*)

EXTENDS CertificateModule,FileOwnershipModule,PriorityModule
(*  Client Consistency Message Support  *)

(*Defn*)AcknowledgementID==Nat

(*Defn*)DistributedPriority==[time:Priority,host:Host]
(*Defn*)MakeDistributedPriority(i_time,i_host)==[time|->i_time,host|->i_host]

(*Defn*)MTOpenFileOperation=="MTOpenFileOperation"
(*Defn*)MTCleanupFileOperation=="MTCleanupFileOperation"
(*Defn*)MTCloseFileOperation=="MTCloseFileOperation"
(*Defn*)MTCloseAndUnlinkFileOperation=="MTCloseAndUnlinkFileOperation"
(*Defn*)MTWriteFileOperation=="MTWriteFileOperation"
(*Defn*)MTCreateFileOperation=="MTCreateFileOperation"
(*Defn*)MTDeleteFileOperation=="MTDeleteFileOperation"
(*Defn*)MTMoveFileOperation=="MTMoveFileOperation"
(*Defn*)MTLeaseRelease=="MTLeaseRelease"
(*Defn*)MTBatchUpdate=="MTBatchUpdate"
(*Defn*)MTLeaseRecall=="MTLeaseRecall"
(*Defn*)MTLeaseRecallDunnit=="MTLeaseRecallDunnit"
(*Defn*)MTSingletonLeaseGrant=="MTSingletonLeaseGrant"
(*Defn*)MTInfiniteChildLeaseGrant=="MTInfiniteChildLeaseGrant"
(*Defn*)MTOpenFileRequest=="MTOpenFileRequest"
(*Defn*)MTCleanupFileRequest=="MTCleanupFileRequest"
(*Defn*)MTCloseFileRequest=="MTCloseFileRequest"
(*Defn*)MTReadFileRequest=="MTReadFileRequest"
(*Defn*)MTWriteFileRequest=="MTWriteFileRequest"
(*Defn*)MTCreateFileRequest=="MTCreateFileRequest"
(*Defn*)MTDeleteFileRequest=="MTDeleteFileRequest"
(*Defn*)MTMoveFileRequest=="MTMoveFileRequest"
(*Defn*)MTUnlinkChildRequest=="MTUnlinkChildRequest"
(*Defn*)MTLinkChildRequest=="MTLinkChildRequest"
(*Defn*)MTResolveLabelRequest=="MTResolveLabelRequest"
(*Defn*)MTIdentifyParentRequest=="MTIdentifyParentRequest"
(*Defn*)MTHint=="MTHint"
(*Defn*)MTHintAcknowledgement=="MTHintAcknowledgement"
(*Defn*)MTLeaseExtensionRequest=="MTLeaseExtensionRequest"
(*Defn*)MTOpenHandleReadSelfRequest=="MTOpenHandleReadSelfRequest"
(*Defn*)MTBonaFideRequest=="MTBonaFideRequest"
(*Defn*)MTPositiveAcknowledgement=="MTPositiveAcknowledgement"
(*Defn*)MTNegativeAcknowledgement=="MTNegativeAcknowledgement"
(*Defn*)MTFileOwnershipLoanGrant=="MTFileOwnershipLoanGrant"
(*Defn*)MTFileOwnershipLoanRequest=="MTFileOwnershipLoanRequest"
(*Defn*)MTFileOwnershipQuery=="MTFileOwnershipQuery"
(*Defn*)MTFileOwnershipNotification=="MTFileOwnershipNotification"
(*Defn*)MTCertificate=="MTCertificate"
(*Defn*)MessageType==
  {
  MTOpenFileOperation,
  MTCleanupFileOperation,
  MTCloseFileOperation,
  MTCloseAndUnlinkFileOperation,
  MTWriteFileOperation,
  MTCreateFileOperation,
  MTDeleteFileOperation,
  MTMoveFileOperation,
  MTLeaseRelease,
  MTBatchUpdate,
  MTLeaseRecall,
  MTLeaseRecallDunnit,
  MTSingletonLeaseGrant,
  MTInfiniteChildLeaseGrant,
  MTOpenFileRequest,
  MTCleanupFileRequest,
  MTCloseFileRequest,
  MTReadFileRequest,
  MTWriteFileRequest,
  MTCreateFileRequest,
  MTDeleteFileRequest,
  MTMoveFileRequest,
  MTUnlinkChildRequest,
  MTLinkChildRequest,
  MTResolveLabelRequest,
  MTIdentifyParentRequest,
  MTHint,
  MTHintAcknowledgement,
  MTLeaseExtensionRequest,
  MTOpenHandleReadSelfRequest,
  MTBonaFideRequest,
  MTPositiveAcknowledgement,
  MTNegativeAcknowledgement,
  MTFileOwnershipLoanGrant,
  MTFileOwnershipLoanRequest,
  MTFileOwnershipQuery,
  MTFileOwnershipNotification,
  MTCertificate
  }

(*Defn*)UPNotLastHandle=="UPNotLastHandle"
(*Defn*)UPDelDispFalse=="UPDelDispFalse"
(*Defn*)UPOtherHandleOpen=="UPOtherHandleOpen"
(*Defn*)UnlinkPreclusion=={UPNotLastHandle,UPDelDispFalse,UPOtherHandleOpen}

(*Defn*)CAUDChildFile=="CAUDChildFile"
(*Defn*)CAUDParentFile=="CAUDParentFile"
(*Defn*)CloseAndUnlinkDestinationField=={CAUDChildFile,CAUDParentFile}

(*Defn*)MDChildFile=="MDChildFile"
(*Defn*)MDSrcParentFile=="MDSrcParentFile"
(*Defn*)MDDestParentFile=="MDDestParentFile"
(*Defn*)MoveDestinationField=={MDChildFile,MDSrcParentFile,MDDestParentFile}

(*Defn*)ChildValue==[label:Label,value:FileID]
(*Defn*)MakeChildValue(i_label,i_value)==[label|->i_label,value|->i_value]

(*  Next idiom: SetOf-something, SeqOf-something  *)

(*Defn*)ChildValueSet==SUBSET ChildValue

(*Defn*)AcknowledgementIDSet==SUBSET AcknowledgementID

(*Defn*)ZeroAckId==0

(*Defn*)CCMAckIDField=="ackID"

(*  Common Messages for Clients and Servers  *)

(*Defn*)OpenFileOperationMessage==
  [
    type:{MTOpenFileOperation},
    expiration:ClosedTime,
    ackID:AcknowledgementID,
    fileID:FileID,
    handle:Handle,
    firstHandle:Boolean,
    modes:ModeSet,
    firstModes:ModeSet
  ]
(*Defn*)OpenFileOperationMessage_destinationFile(this)==this.fileID
(*Defn*)
MakeOpenFileOperationMessage(
  i_fileID,i_handle,i_firstHandle,i_modes,i_firstModes)==
  [
  type|->MTOpenFileOperation,
  fileID|->i_fileID,
  handle|->i_handle,
  firstHandle|->i_firstHandle,
  modes|->i_modes,
  firstModes|->i_firstModes
  ]

(*Defn*)CleanupFileOperationMessage==
  [
    type:{MTCleanupFileOperation},
    expiration:ClosedTime,
    ackID:AcknowledgementID,
    fileID:FileID,
    handle:Handle,
    modes:ModeSet,
    lastModes:ModeSet
  ]
(*Defn*)CleanupFileOperationMessage_destinationFile(this)==this.fileID
(*Defn*)
MakeCleanupFileOperationMessage(i_fileID,i_handle,i_modes,i_lastModes)==
  [
  type|->MTCleanupFileOperation,
  fileID|->i_fileID,
  handle|->i_handle,
  modes|->i_modes,
  lastModes|->i_lastModes
  ]

(*Defn*)CloseFileOperationMessage==
  [
    type:{MTCloseFileOperation},
    expiration:ClosedTime,
    ackID:AcknowledgementID,
    fileID:FileID,
    handle:Handle,
    unlinkPreclusion:UnlinkPreclusion
  ]
(*Defn*)CloseFileOperationMessage_destinationFile(this)==this.fileID
(*Defn*)MakeCloseFileOperationMessage(i_fileID,i_handle,i_unlinkPreclusion)==
  [
  type|->MTCloseFileOperation,
  fileID|->i_fileID,
  handle|->i_handle,
  unlinkPreclusion|->i_unlinkPreclusion
  ]

(*Defn*)CloseAndUnlinkFileOperationMessage==
  [
    type:{MTCloseAndUnlinkFileOperation},
    expiration:ClosedTime,
    ackID:AcknowledgementID,
    destination:CloseAndUnlinkDestinationField,
    childFile:FileID,
    parentFile:FileID,
    handle:Handle,
    label:Label
  ]
(*Defn*)CloseAndUnlinkFileOperationMessage_destinationFile(this)==
  IF this.destination=CAUDChildFile THEN this.childFile ELSE this.parentFile
(*Defn*)
MakeCloseAndUnlinkFileOperationMessage(
  i_destination,i_childFile,i_parentFile,i_handle,i_label)==
  [
  type|->MTCloseAndUnlinkFileOperation,
  destination|->i_destination,
  childFile|->i_childFile,
  parentFile|->i_parentFile,
  handle|->i_handle,
  label|->i_label
  ]

(*Defn*)WriteFileOperationMessage==
  [
    type:{MTWriteFileOperation},
    expiration:ClosedTime,
    ackID:AcknowledgementID,
    fileID:FileID,
    handle:Handle,
    content:Content
  ]
(*Defn*)WriteFileOperationMessage_destinationFile(this)==this.fileID
(*Defn*)MakeWriteFileOperationMessage(i_fileID,i_handle,i_content)==
  [
  type|->MTWriteFileOperation,
  fileID|->i_fileID,
  handle|->i_handle,
  content|->i_content
  ]

(*Defn*)CreateFileOperationMessage==
  [
    type:{MTCreateFileOperation},
    expiration:ClosedTime,
    ackID:AcknowledgementID,
    fileID:FileID,
    parentFile:FileID,
    label:Label,
    handle:Handle,
    modes:ModeSet,
    sharedValueLeaseTime:ClosedTime,
    blackBoxReadSelfLeaseTime:ClosedTime,
    blackBoxWriteSelfLeaseTime:ClosedTime,
    blackBoxReadOtherLeaseTime:ClosedTime,
    privateValueLeaseTime:ClosedTime,
    borrowedMaxSuffix:FileIDComponent
  ]
(*Defn*)CreateFileOperationMessage_destinationFile(this)==this.parentFile
(*Defn*)
MakeCreateFileOperationMessage(
  i_fileID,
  i_parentFile,
  i_label,
  i_handle,
  i_modes,
  i_sharedValueLeaseTime,
  i_blackBoxReadSelfLeaseTime,
  i_blackBoxWriteSelfLeaseTime,
  i_blackBoxReadOtherLeaseTime,
  i_privateValueLeaseTime,
  i_borrowedMaxSuffix)==
  [
  type|->MTCreateFileOperation,
  fileID|->i_fileID,
  parentFile|->i_parentFile,
  label|->i_label,
  handle|->i_handle,
  modes|->i_modes,
  sharedValueLeaseTime|->i_sharedValueLeaseTime,
  blackBoxReadSelfLeaseTime|->i_blackBoxReadSelfLeaseTime,
  blackBoxWriteSelfLeaseTime|->i_blackBoxWriteSelfLeaseTime,
  blackBoxReadOtherLeaseTime|->i_blackBoxReadOtherLeaseTime,
  privateValueLeaseTime|->i_privateValueLeaseTime,
  borrowedMaxSuffix|->i_borrowedMaxSuffix
  ]

(*Defn*)DeleteFileOperationMessage==
  [
    type:{MTDeleteFileOperation},
    expiration:ClosedTime,
    ackID:AcknowledgementID,
    fileID:FileID,
    handle:Handle,
    delDisp:Boolean
  ]
(*Defn*)DeleteFileOperationMessage_destinationFile(this)==this.fileID
(*Defn*)MakeDeleteFileOperationMessage(i_fileID,i_handle,i_delDisp)==
  [
  type|->MTDeleteFileOperation,
  fileID|->i_fileID,
  handle|->i_handle,
  delDisp|->i_delDisp
  ]

(*Defn*)MoveFileOperationMessage==
  [
    type:{MTMoveFileOperation},
    expiration:ClosedTime,
    ackID:AcknowledgementID,
    destination:MoveDestinationField,
    childFile:FileID,
    childHandle:Handle,
    srcParentFile:FileID,
    srcLabel:Label,
    destParentFile:FileID,
    destLabel:Label
  ]
(*Defn*)MoveFileOperationMessage_destinationFile(this)==
  IF this.destination=MDChildFile
  THEN
    this.childFile
  ELSE IF this.destination=MDSrcParentFile
  THEN
    this.srcParentFile
  ELSE
    this.destParentFile
(*Defn*)
MakeMoveFileOperationMessage(
  i_destination,
  i_childFile,
  i_childHandle,
  i_srcParentFile,
  i_srcLabel,
  i_destParentFile,
  i_destLabel)==
  [
  type|->MTMoveFileOperation,
  destination|->i_destination,
  childFile|->i_childFile,
  childHandle|->i_childHandle,
  srcParentFile|->i_srcParentFile,
  srcLabel|->i_srcLabel,
  destParentFile|->i_destParentFile,
  destLabel|->i_destLabel
  ]
(*Defn*)OperationMessage==
  UNION
  {
  OpenFileOperationMessage,
  CleanupFileOperationMessage,
  CloseFileOperationMessage,
  CloseAndUnlinkFileOperationMessage,
  WriteFileOperationMessage,
  CreateFileOperationMessage,
  DeleteFileOperationMessage,
  MoveFileOperationMessage
  }

(*Defn*)LeaseReleaseMessage==
  [
    type:{MTLeaseRelease},
    expiration:ClosedTime,
    ackID:AcknowledgementID,
    fileField:FileField,
    rw:PReadOrWrite
  ]
(*Defn*)MakeLeaseReleaseMessage(i_fileField,i_rw)==
  [type|->MTLeaseRelease,fileField|->i_fileField,rw|->i_rw]
(*Defn*)ClientConsistencyMessage==UNION{OperationMessage,LeaseReleaseMessage}
(*Defn*)ClientConsistencyMessage_destinationFile(this)==
  IF this \in OpenFileOperationMessage
  THEN
    this.fileID
  ELSE IF this \in CleanupFileOperationMessage
  THEN
    this.fileID
  ELSE IF this \in CloseFileOperationMessage
  THEN
    this.fileID
  ELSE IF this \in CloseAndUnlinkFileOperationMessage
  THEN
    IF this.destination=CAUDChildFile THEN this.childFile ELSE this.parentFile
  ELSE IF this \in WriteFileOperationMessage
  THEN
    this.fileID
  ELSE IF this \in CreateFileOperationMessage
  THEN
    this.parentFile
  ELSE IF this \in DeleteFileOperationMessage
  THEN
    this.fileID
  ELSE IF this \in MoveFileOperationMessage
  THEN
    IF this.destination=MDChildFile
    THEN
      this.childFile
    ELSE IF this.destination=MDSrcParentFile
    THEN
      this.srcParentFile
    ELSE
      this.destParentFile
  ELSE
    this.fileField.fileID
(*Defn*)ClientConsistencyMessageSeq==ArbSeq(ClientConsistencyMessage)

(*Defn*)BatchUpdateMessage==
  [type:{MTBatchUpdate},batch:ClientConsistencyMessageSeq]
(*Defn*)MakeBatchUpdateMessage(i_batch)==
  [type|->MTBatchUpdate,batch|->i_batch]

(*Defn*)LeaseRecallMessage==
  [
    type:{MTLeaseRecall},
    fileField:FileField,
    rw:PReadOrWrite,
    priority:DistributedPriority
  ]
(*Defn*)MakeLeaseRecallMessage(i_fileField,i_rw,i_priority)==
  [
  type|->MTLeaseRecall,
  fileField|->i_fileField,
  rw|->i_rw,
  priority|->i_priority
  ]

(*Defn*)LeaseRecallDunnitMessage==
  [type:{MTLeaseRecallDunnit},recall:LeaseRecallMessage]
(*Defn*)MakeLeaseRecallDunnitMessage(i_recall)==
  [type|->MTLeaseRecallDunnit,recall|->i_recall]

(*Defn*)SingletonLeaseGrantMessage==
  [
    type:{MTSingletonLeaseGrant},
    fileField:FileSingletonField,
    rw:PReadOrWrite,
    value:FileValueType,
    extension:Boolean,
    expiration:ClosedTime
  ]
(*Defn*)
MakeSingletonLeaseGrantMessage(
  i_fileField,i_rw,i_value,i_extension,i_expiration)==
  [
  type|->MTSingletonLeaseGrant,
  fileField|->i_fileField,
  rw|->i_rw,
  value|->i_value,
  extension|->i_extension,
  expiration|->i_expiration
  ]

(*Defn*)InfiniteChildLeaseGrantMessage==
  [
    type:{MTInfiniteChildLeaseGrant},
    fileField:FileInfiniteChildField,
    childValueSet:ChildValueSet,
    extension:Boolean,
    expiration:ClosedTime
  ]
(*Defn*)
MakeInfiniteChildLeaseGrantMessage(
  i_fileField,i_childValueSet,i_extension,i_expiration)==
  [
  type|->MTInfiniteChildLeaseGrant,
  fileField|->i_fileField,
  childValueSet|->i_childValueSet,
  extension|->i_extension,
  expiration|->i_expiration
  ]
(*Defn*)LeaseGrantMessage==
  UNION{SingletonLeaseGrantMessage,InfiniteChildLeaseGrantMessage}

(*Defn*)OpenFileRequestMessage==
  [
    type:{MTOpenFileRequest},
    fileID:FileID,
    priority:DistributedPriority,
    firstHandle:Boolean,
    modes:ModeSet,
    firstModes:ModeSet
  ]
(*Defn*)
MakeOpenFileRequestMessage(
  i_fileID,i_priority,i_firstHandle,i_modes,i_firstModes)==
  [
  type|->MTOpenFileRequest,
  firstHandle|->i_firstHandle,
  modes|->i_modes,
  firstModes|->i_firstModes
  ]

(*Defn*)CleanupFileRequestMessage==
  [
    type:{MTCleanupFileRequest},
    fileID:FileID,
    priority:DistributedPriority,
    handle:Handle,
    lastModes:ModeSet
  ]
(*Defn*)
MakeCleanupFileRequestMessage(i_fileID,i_priority,i_handle,i_lastModes)==
  [type|->MTCleanupFileRequest,handle|->i_handle,lastModes|->i_lastModes]

(*Defn*)CloseFileRequestMessage==
  [
    type:{MTCloseFileRequest},
    fileID:FileID,
    priority:DistributedPriority,
    handle:Handle
  ]
(*Defn*)MakeCloseFileRequestMessage(i_fileID,i_priority,i_handle)==
  [type|->MTCloseFileRequest,handle|->i_handle]
(*Defn*)ReadFileRequestMessage==
  [type:{MTReadFileRequest},fileID:FileID,priority:DistributedPriority]
(*Defn*)MakeReadFileRequestMessage(i_fileID,i_priority)==
  [type|->MTReadFileRequest]
(*Defn*)WriteFileRequestMessage==
  [type:{MTWriteFileRequest},fileID:FileID,priority:DistributedPriority]
(*Defn*)MakeWriteFileRequestMessage(i_fileID,i_priority)==
  [type|->MTWriteFileRequest]

(*Defn*)CreateFileRequestMessage==
  [
    type:{MTCreateFileRequest},
    fileID:FileID,
    priority:DistributedPriority,
    label:Label
  ]
(*Defn*)MakeCreateFileRequestMessage(i_fileID,i_priority,i_label)==
  [type|->MTCreateFileRequest,label|->i_label]

(*Defn*)DeleteFileRequestMessage==
  [
    type:{MTDeleteFileRequest},
    fileID:FileID,
    priority:DistributedPriority,
    delDisp:Boolean
  ]
(*Defn*)MakeDeleteFileRequestMessage(i_fileID,i_priority,i_delDisp)==
  [type|->MTDeleteFileRequest,delDisp|->i_delDisp]
(*Defn*)MoveFileRequestMessage==
  [type:{MTMoveFileRequest},fileID:FileID,priority:DistributedPriority]
(*Defn*)MakeMoveFileRequestMessage(i_fileID,i_priority)==
  [type|->MTMoveFileRequest]

(*Defn*)UnlinkChildRequestMessage==
  [
    type:{MTUnlinkChildRequest},
    fileID:FileID,
    priority:DistributedPriority,
    label:Label
  ]
(*Defn*)MakeUnlinkChildRequestMessage(i_fileID,i_priority,i_label)==
  [type|->MTUnlinkChildRequest,label|->i_label]

(*Defn*)LinkChildRequestMessage==
  [
    type:{MTLinkChildRequest},
    fileID:FileID,
    priority:DistributedPriority,
    label:Label
  ]
(*Defn*)MakeLinkChildRequestMessage(i_fileID,i_priority,i_label)==
  [type|->MTLinkChildRequest,label|->i_label]

(*Defn*)ResolveLabelRequestMessage==
  [
    type:{MTResolveLabelRequest},
    fileID:FileID,
    priority:DistributedPriority,
    label:Label
  ]
(*Defn*)MakeResolveLabelRequestMessage(i_fileID,i_priority,i_label)==
  [type|->MTResolveLabelRequest,label|->i_label]
(*Defn*)IdentifyParentRequestMessage==
  [type:{MTIdentifyParentRequest},fileID:FileID,priority:DistributedPriority]
(*Defn*)MakeIdentifyParentRequestMessage(i_fileID,i_priority)==
  [type|->MTIdentifyParentRequest]
(*Defn*)LeaseRequestMessage==
  UNION
  {
  OpenFileRequestMessage,
  CleanupFileRequestMessage,
  CloseFileRequestMessage,
  ReadFileRequestMessage,
  WriteFileRequestMessage,
  CreateFileRequestMessage,
  DeleteFileRequestMessage,
  MoveFileRequestMessage,
  UnlinkChildRequestMessage,
  LinkChildRequestMessage,
  ResolveLabelRequestMessage,
  IdentifyParentRequestMessage
  }

(*Defn*)HintMessage==
  [type:{MTHint},hintID:AcknowledgementID,request:LeaseRequestMessage]
(*Defn*)MakeHintMessage(i_hintID,i_request)==
  [type|->MTHint,hintID|->i_hintID,request|->i_request]

(*Defn*)HintAcknowledgementMessage==
  [type:{MTHintAcknowledgement},hintID:AcknowledgementID]
(*Defn*)MakeHintAcknowledgementMessage(i_hintID)==
  [type|->MTHintAcknowledgement,hintID|->i_hintID]

(*Defn*)LeaseExtensionRequestMessage==
  [type:{MTLeaseExtensionRequest},fileField:FileSingletonField,rw:PReadOrWrite]
(*Defn*)MakeLeaseExtensionRequestMessage(i_fileField,i_rw)==
  [type|->MTLeaseExtensionRequest,fileField|->i_fileField,rw|->i_rw]

(*Defn*)OpenHandleReadSelfRequestMessage==
  [type:{MTOpenHandleReadSelfRequest},fileID:FileID]
(*Defn*)MakeOpenHandleReadSelfRequestMessage(i_fileID)==
  [type|->MTOpenHandleReadSelfRequest,fileID|->i_fileID]

(*Defn*)BonaFideRequestMessage==[type:{MTBonaFideRequest},fileID:FileID]
(*Defn*)MakeBonaFideRequestMessage(i_fileID)==
  [type|->MTBonaFideRequest,fileID|->i_fileID]

(*Defn*)PositiveAcknowledgementMessage==
  [type:{MTPositiveAcknowledgement},ackID:AcknowledgementID]
(*Defn*)MakePositiveAcknowledgementMessage(i_ackID)==
  [type|->MTPositiveAcknowledgement,ackID|->i_ackID]

(*Defn*)NegativeAcknowledgementMessage==
  [type:{MTNegativeAcknowledgement},ackID:AcknowledgementIDSet]
(*Defn*)MakeNegativeAcknowledgementMessage(i_ackID)==
  [type|->MTNegativeAcknowledgement,ackID|->i_ackID]
(*Defn*)AcknowledgementMessage==
  UNION{PositiveAcknowledgementMessage,NegativeAcknowledgementMessage}

(*Defn*)FileOwnershipLoanGrantMessage==
  [
    type:{MTFileOwnershipLoanGrant},
    iparentFile:FileID,
    minSuffix:FileIDComponent,
    maxSuffix:FileIDComponent
  ]
(*Defn*)
MakeFileOwnershipLoanGrantMessage(i_iparentFile,i_minSuffix,i_maxSuffix)==
  [
  type|->MTFileOwnershipLoanGrant,
  iparentFile|->i_iparentFile,
  minSuffix|->i_minSuffix,
  maxSuffix|->i_maxSuffix
  ]

(*Defn*)FileOwnershipLoanRequestMessage==
  [type:{MTFileOwnershipLoanRequest},iparentFile:FileID]
(*Defn*)MakeFileOwnershipLoanRequestMessage(i_iparentFile)==
  [type|->MTFileOwnershipLoanRequest,iparentFile|->i_iparentFile]

(*Defn*)FileOwnershipQueryMessage==
  [type:{MTFileOwnershipQuery},fileID:FileID]
(*Defn*)MakeFileOwnershipQueryMessage(i_fileID)==
  [type|->MTFileOwnershipQuery,fileID|->i_fileID]

(*Defn*)FileOwnershipNotificationMessage==
  [type:{MTFileOwnershipNotification},deed:Deed]
(*Defn*)MakeFileOwnershipNotificationMessage(i_deed)==
  [type|->MTFileOwnershipNotification,deed|->i_deed]
(*Defn*)FileOwnershipMessage==
  UNION
  {
  FileOwnershipLoanGrantMessage,
  FileOwnershipLoanRequestMessage,
  FileOwnershipQueryMessage,
  FileOwnershipNotificationMessage
  }

(*Defn*)CertificateMessage==[type:{MTCertificate},cert:Certificate]
(*Defn*)MakeCertificateMessage(i_cert)==[type|->MTCertificate,cert|->i_cert]
(*Defn*)CommonMessage==
  UNION
  {
  ClientConsistencyMessage,
  BatchUpdateMessage,
  LeaseRecallMessage,
  LeaseRecallDunnitMessage,
  LeaseGrantMessage,
  LeaseRequestMessage,
  HintMessage,
  HintAcknowledgementMessage,
  LeaseExtensionRequestMessage,
  OpenHandleReadSelfRequestMessage,
  BonaFideRequestMessage,
  AcknowledgementMessage,
  FileOwnershipMessage,
  CertificateMessage
  }

(*Defn*)LeaseRecallMessageSet==SUBSET LeaseRecallMessage

(*Defn*)LeaseRequestMessageSet==SUBSET LeaseRequestMessage

(*Defn*)CFSharedValueLeaseTime=="CFSharedValueLeaseTime"
(*Defn*)CFBlackBoxReadSelfLeaseTime=="CFBlackBoxReadSelfLeaseTime"
(*Defn*)CFBlackBoxWriteSelfLeaseTime=="CFBlackBoxWriteSelfLeaseTime"
(*Defn*)CFBlackBoxReadOtherLeaseTime=="CFBlackBoxReadOtherLeaseTime"
(*Defn*)CFPrivateValueLeaseTime=="CFPrivateValueLeaseTime"
(*Defn*)CreateFileMessageLeaseTimeFields==
  {
  CFSharedValueLeaseTime,
  CFBlackBoxReadSelfLeaseTime,
  CFBlackBoxWriteSelfLeaseTime,
  CFBlackBoxReadOtherLeaseTime,
  CFPrivateValueLeaseTime
  }

(*  The following assumption is realized in code as Encode/Decode marshalling methods  *)

ASSUME CommonMessage \subseteq Blob
====
