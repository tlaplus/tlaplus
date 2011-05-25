---- MODULE ServerMessageModule ----
(*`^\addcontentsline{toc}{section}{ServerMessageModule}^'*)

EXTENDS ServerFileProtectionModule
(* ********** Server-to-Server Interlock Messages ************************************************************************** *)

(*Defn*)SIMDeadline=="deadline"

(*Defn*)MTPathRequest=="MTPathRequest"
(*Defn*)MTPathRequestDunnit=="MTPathRequestDunnit"
(*Defn*)MTPathGrant=="MTPathGrant"
(*Defn*)MTPathRelease=="MTPathRelease"
(*Defn*)MTPathRecall=="MTPathRecall"
(*Defn*)MTPathRecallDunnit=="MTPathRecallDunnit"
(*Defn*)MTPathPrompt=="MTPathPrompt"
(*Defn*)MTParentFieldReserved=="MTParentFieldReserved"
(*Defn*)MTParentFieldReservedIndication=="MTParentFieldReservedIndication"
(*Defn*)MTChildFieldReserved=="MTChildFieldReserved"
(*Defn*)MTUpdateParentField=="MTUpdateParentField"
(*Defn*)MTUpdateChildField=="MTUpdateChildField"
(*Defn*)MTUnreserveParentField=="MTUnreserveParentField"
(*Defn*)MTUnreserveChildField=="MTUnreserveChildField"
(*Defn*)MTParentFieldUpdated=="MTParentFieldUpdated"
(*Defn*)MTChildFieldUpdated=="MTChildFieldUpdated"
(*Defn*)MTParentFieldUnreserved=="MTParentFieldUnreserved"
(*Defn*)MTFileOwnershipDelegation=="MTFileOwnershipDelegation"
(*Defn*)MTMCLoadCronTrigger=="MTMCLoadCronTrigger"
(*Defn*)MTMCLoadOffer=="MTMCLoadOffer"
(*Defn*)MTMCLoadReject=="MTMCLoadReject"
(*Defn*)MTMCLoadAccept=="MTMCLoadAccept"
(*Defn*)MTMCLoadTransferComplete=="MTMCLoadTransferComplete"
(*Defn*)MTMCInitiateDelegationRequest=="MTMCInitiateDelegationRequest"
(*Defn*)MTMCInitiateDelegationComplete=="MTMCInitiateDelegationComplete"
(*Defn*)MTMCLoadReportCronTrigger=="MTMCLoadReportCronTrigger"
(*Defn*)MTMCLoadReport=="MTMCLoadReport"
(*Defn*)MTHostIDAllocateRequest=="MTHostIDAllocateRequest"
(*Defn*)MTHostIDAllocateReply=="MTHostIDAllocateReply"
(*Defn*)ServerMessageType==
  {
  MTPathRequest,
  MTPathRequestDunnit,
  MTPathGrant,
  MTPathRelease,
  MTPathRecall,
  MTPathRecallDunnit,
  MTPathPrompt,
  MTParentFieldReserved,
  MTParentFieldReservedIndication,
  MTChildFieldReserved,
  MTUpdateParentField,
  MTUpdateChildField,
  MTUnreserveParentField,
  MTUnreserveChildField,
  MTParentFieldUpdated,
  MTChildFieldUpdated,
  MTParentFieldUnreserved,
  MTFileOwnershipDelegation,
  MTMCLoadCronTrigger,
  MTMCLoadOffer,
  MTMCLoadReject,
  MTMCLoadAccept,
  MTMCLoadTransferComplete,
  MTMCInitiateDelegationRequest,
  MTMCInitiateDelegationComplete,
  MTMCLoadReportCronTrigger,
  MTMCLoadReport,
  MTHostIDAllocateRequest,
  MTHostIDAllocateReply
  }

(* 
	jonh moved these definitions outside the struct to work around
	a bug in Sany's emitIdioms mechanisms.
 *)

(*Defn*)FileValueData==UNION{[fileSet->FileValue]:fileSet \in SUBSET FileID}

(*Defn*)FileProtectionData==
  UNION{[fileSet->FileProtection]:fileSet \in SUBSET FileID}

(*Defn*)PathRequestMessage==
  [
    type:{MTPathRequest},
    destFile:FileID,
    srcFile:FileID,
    priority:DistributedPriority,
    label:Label
  ]
(*Defn*)MakePathRequestMessage(i_destFile,i_srcFile,i_priority,i_label)==
  [type|->MTPathRequest,label|->i_label]
(*Defn*)PathRecallMessage==
  [
    type:{MTPathRecall},
    destFile:FileID,
    srcFile:FileID,
    priority:DistributedPriority
  ]
(*Defn*)MakePathRecallMessage(i_destFile,i_srcFile,i_priority)==
  [type|->MTPathRecall]
(*Defn*)PathHintMessage==UNION{PathRequestMessage,PathRecallMessage}

(*Defn*)PathRequestDunnitMessage==
  [
    type:{MTPathRequestDunnit},
    destFile:FileID,
    srcFile:FileID,
    request:PathRequestMessage
  ]
(*Defn*)MakePathRequestDunnitMessage(i_destFile,i_srcFile,i_request)==
  [type|->MTPathRequestDunnit,request|->i_request]

(*Defn*)PathRecallDunnitMessage==
  [
    type:{MTPathRecallDunnit},
    destFile:FileID,
    srcFile:FileID,
    recall:PathRecallMessage
  ]
(*Defn*)MakePathRecallDunnitMessage(i_destFile,i_srcFile,i_recall)==
  [type|->MTPathRecallDunnit,recall|->i_recall]

(*Defn*)PathGrantMessage==
  [
    type:{MTPathGrant},
    destFile:FileID,
    srcFile:FileID,
    ancestors:FileSeq,
    extension:Boolean,
    deadline:ClosedTime
  ]
(*Defn*)PathGrantMessage_GetDeadline(this)==this.deadline
(*Defn*)PathGrantMessage_NeuterDeadline(this)==TRUE
(*Defn*)
MakePathGrantMessage(
  i_destFile,i_srcFile,i_ancestors,i_extension,i_deadline)==
  [
  type|->MTPathGrant,
  ancestors|->i_ancestors,
  extension|->i_extension,
  deadline|->i_deadline
  ]

(*Defn*)PathReleaseMessage==
  [type:{MTPathRelease},destFile:FileID,srcFile:FileID,deadline:ClosedTime]
(*Defn*)PathReleaseMessage_GetDeadline(this)==this.deadline
(*Defn*)PathReleaseMessage_NeuterDeadline(this)==TRUE
(*Defn*)MakePathReleaseMessage(i_destFile,i_srcFile,i_deadline)==
  [type|->MTPathRelease,deadline|->i_deadline]

(*Defn*)ParentFieldReservedMessage==
  [
    type:{MTParentFieldReserved},
    destFile:FileID,
    srcFile:FileID,
    reservation:Parent,
    initiator:Client,
    deadline:ClosedTime
  ]
(*Defn*)ParentFieldReservedMessage_GetDeadline(this)==this.deadline
(*Defn*)ParentFieldReservedMessage_NeuterDeadline(this)==TRUE
(*Defn*)
MakeParentFieldReservedMessage(
  i_destFile,i_srcFile,i_reservation,i_initiator,i_deadline)==
  [
  type|->MTParentFieldReserved,
  reservation|->i_reservation,
  initiator|->i_initiator,
  deadline|->i_deadline
  ]

(*Defn*)ParentFieldReservedIndicationMessage==
  [
    type:{MTParentFieldReservedIndication},
    destFile:FileID,
    srcFile:FileID,
    reservation:Parent,
    initiator:Client
  ]
(*Defn*)
MakeParentFieldReservedIndicationMessage(
  i_destFile,i_srcFile,i_reservation,i_initiator)==
  [
  type|->MTParentFieldReservedIndication,
  reservation|->i_reservation,
  initiator|->i_initiator
  ]

(*Defn*)ChildFieldReservedMessage==
  [
    type:{MTChildFieldReserved},
    destFile:FileID,
    srcFile:FileID,
    label:Label,
    reservation:FileOrNil,
    initiator:Client,
    deadline:ClosedTime
  ]
(*Defn*)ChildFieldReservedMessage_GetDeadline(this)==this.deadline
(*Defn*)ChildFieldReservedMessage_NeuterDeadline(this)==TRUE
(*Defn*)
MakeChildFieldReservedMessage(
  i_destFile,i_srcFile,i_label,i_reservation,i_initiator,i_deadline)==
  [
  type|->MTChildFieldReserved,
  label|->i_label,
  reservation|->i_reservation,
  initiator|->i_initiator,
  deadline|->i_deadline
  ]

(*Defn*)UpdateParentFieldMessage==
  [
    type:{MTUpdateParentField},
    destFile:FileID,
    srcFile:FileID,
    label:LabelOrNil,
    newFile:FileOrNil,
    initiator:Client
  ]
(*Defn*)
MakeUpdateParentFieldMessage(
  i_destFile,i_srcFile,i_label,i_newFile,i_initiator)==
  [
  type|->MTUpdateParentField,
  label|->i_label,
  newFile|->i_newFile,
  initiator|->i_initiator
  ]

(*Defn*)UpdateChildFieldMessage==
  [
    type:{MTUpdateChildField},
    destFile:FileID,
    srcFile:FileID,
    label:Label,
    newFile:FileID,
    initiator:Client
  ]
(*Defn*)
MakeUpdateChildFieldMessage(
  i_destFile,i_srcFile,i_label,i_newFile,i_initiator)==
  [
  type|->MTUpdateChildField,
  label|->i_label,
  newFile|->i_newFile,
  initiator|->i_initiator
  ]
(*Defn*)UnreserveParentFieldMessage==
  [type:{MTUnreserveParentField},destFile:FileID,srcFile:FileID]
(*Defn*)MakeUnreserveParentFieldMessage(i_destFile,i_srcFile)==
  [type|->MTUnreserveParentField]

(*Defn*)UnreserveChildFieldMessage==
  [type:{MTUnreserveChildField},destFile:FileID,srcFile:FileID,label:Label]
(*Defn*)MakeUnreserveChildFieldMessage(i_destFile,i_srcFile,i_label)==
  [type|->MTUnreserveChildField,label|->i_label]

(*Defn*)ParentFieldUpdatedMessage==
  [
    type:{MTParentFieldUpdated},
    destFile:FileID,
    srcFile:FileID,
    newLabel:Label,
    newFile:FileID
  ]
(*Defn*)
MakeParentFieldUpdatedMessage(i_destFile,i_srcFile,i_newLabel,i_newFile)==
  [type|->MTParentFieldUpdated,newLabel|->i_newLabel,newFile|->i_newFile]

(*Defn*)ChildFieldUpdatedMessage==
  [
    type:{MTChildFieldUpdated},
    destFile:FileID,
    srcFile:FileID,
    label:Label,
    newFile:FileID
  ]
(*Defn*)
MakeChildFieldUpdatedMessage(i_destFile,i_srcFile,i_label,i_newFile)==
  [type|->MTChildFieldUpdated,label|->i_label,newFile|->i_newFile]
(*Defn*)ParentFieldUnreservedMessage==
  [type:{MTParentFieldUnreserved},destFile:FileID,srcFile:FileID]
(*Defn*)MakeParentFieldUnreservedMessage(i_destFile,i_srcFile)==
  [type|->MTParentFieldUnreserved]
(*Defn*)ServerInterlockMessage==
  UNION
  {
  PathHintMessage,
  PathRequestDunnitMessage,
  PathRecallDunnitMessage,
  PathGrantMessage,
  PathReleaseMessage,
  ParentFieldReservedMessage,
  ParentFieldReservedIndicationMessage,
  ChildFieldReservedMessage,
  UpdateParentFieldMessage,
  UpdateChildFieldMessage,
  UnreserveParentFieldMessage,
  UnreserveChildFieldMessage,
  ParentFieldUpdatedMessage,
  ChildFieldUpdatedMessage,
  ParentFieldUnreservedMessage
  }

(*Defn*)FileOwnershipDelegationMessage==
  [
    type:{MTFileOwnershipDelegation},
    fileMap:FileMappingSet,
    fileValueData:FileValueData,
    fileProtectionData:FileProtectionData,
    borrowerRecordSet:BorrowerRecordSet
  ]
(*Defn*)
MakeFileOwnershipDelegationMessage(
  i_fileMap,i_fileValueData,i_fileProtectionData,i_borrowerRecordSet)==
  [
  type|->MTFileOwnershipDelegation,
  fileMap|->i_fileMap,
  fileValueData|->i_fileValueData,
  fileProtectionData|->i_fileProtectionData,
  borrowerRecordSet|->i_borrowerRecordSet
  ]
(*Defn*)MCLoadCronTriggerMessage==[type:{MTMCLoadCronTrigger}]
(*Defn*)MakeMCLoadCronTriggerMessage==[type|->MTMCLoadCronTrigger]

(*Defn*)MCLoadOfferMessage==
  [type:{MTMCLoadOffer},maxLoad:LoadValue,delegateFromHost:Host]
(*Defn*)MakeMCLoadOfferMessage(i_maxLoad,i_delegateFromHost)==
  [
  type|->MTMCLoadOffer,
  maxLoad|->i_maxLoad,
  delegateFromHost|->i_delegateFromHost
  ]
(*Defn*)MCLoadRejectMessage==[type:{MTMCLoadReject}]
(*Defn*)MakeMCLoadRejectMessage==[type|->MTMCLoadReject]

(*Defn*)MCLoadAcceptMessage==
  [
    type:{MTMCLoadAccept},
    delegateFromHost:Host,
    lowLoad:LoadValue,
    newHost:Host,
    newMachine:Machine
  ]
(*Defn*)
MakeMCLoadAcceptMessage(
  i_delegateFromHost,i_lowLoad,i_newHost,i_newMachine)==
  [
  type|->MTMCLoadAccept,
  delegateFromHost|->i_delegateFromHost,
  lowLoad|->i_lowLoad,
  newHost|->i_newHost,
  newMachine|->i_newMachine
  ]
(*Defn*)MCLoadTransferCompleteMessage==[type:{MTMCLoadTransferComplete}]
(*Defn*)MakeMCLoadTransferCompleteMessage==[type|->MTMCLoadTransferComplete]

(*Defn*)MCInitiateDelegationRequestMessage==
  [
    type:{MTMCInitiateDelegationRequest},
    maxLoad:LoadValue,
    lowLoad:LoadValue,
    newHost:Host,
    newMachine:Machine
  ]
(*Defn*)
MakeMCInitiateDelegationRequestMessage(
  i_maxLoad,i_lowLoad,i_newHost,i_newMachine)==
  [
  type|->MTMCInitiateDelegationRequest,
  maxLoad|->i_maxLoad,
  lowLoad|->i_lowLoad,
  newHost|->i_newHost,
  newMachine|->i_newMachine
  ]

(*Defn*)MCInitiateDelegationCompleteMessage==
  [type:{MTMCInitiateDelegationComplete},status:Boolean]
(*Defn*)MakeMCInitiateDelegationCompleteMessage(i_status)==
  [type|->MTMCInitiateDelegationComplete,status|->i_status]
(*Defn*)MCLoadReportCronTriggerMessage==[type:{MTMCLoadReportCronTrigger}]
(*Defn*)MakeMCLoadReportCronTriggerMessage==
  [type|->MTMCLoadReportCronTrigger]

(*Defn*)MCLoadReportMessage==[type:{MTMCLoadReport},hostLoad:LoadValue]
(*Defn*)MakeMCLoadReportMessage(i_hostLoad)==
  [type|->MTMCLoadReport,hostLoad|->i_hostLoad]

(*Defn*)HostIDAllocateRequestMessage==
  [type:{MTHostIDAllocateRequest},machine:Machine]
(*Defn*)MakeHostIDAllocateRequestMessage(i_machine)==
  [type|->MTHostIDAllocateRequest,machine|->i_machine]

(*Defn*)HostIDAllocateReplyMessage==
  [type:{MTHostIDAllocateReply},newHostID:Host]
(*Defn*)MakeHostIDAllocateReplyMessage(i_newHostID)==
  [type|->MTHostIDAllocateReply,newHostID|->i_newHostID]
(*Defn*)ServerMessage==
  UNION
  {
  ServerInterlockMessage,
  FileOwnershipDelegationMessage,
  MCLoadCronTriggerMessage,
  MCLoadOfferMessage,
  MCLoadRejectMessage,
  MCLoadAcceptMessage,
  MCLoadTransferCompleteMessage,
  MCInitiateDelegationRequestMessage,
  MCInitiateDelegationCompleteMessage,
  MCLoadReportCronTriggerMessage,
  MCLoadReportMessage,
  HostIDAllocateRequestMessage,
  HostIDAllocateReplyMessage
  }
(*Defn*)ServerMessage_GetDeadline(this)==
  IF this \in ServerMessage
  THEN
    AfterTimeEnds
  ELSE IF this \in PathGrantMessage
  THEN
    this.deadline
  ELSE IF this \in PathReleaseMessage
  THEN
    this.deadline
  ELSE IF this \in ParentFieldReservedMessage
  THEN
    this.deadline
  ELSE
    this.deadline
(*Defn*)ServerMessage_NeuterDeadline(this)==
  IF this \in ServerMessage
  THEN
    TRUE
  ELSE IF this \in PathGrantMessage
  THEN
    TRUE
  ELSE IF this \in PathReleaseMessage
  THEN
    TRUE
  ELSE IF this \in ParentFieldReservedMessage
  THEN
    TRUE
  ELSE
    TRUE

(*Defn*)ServerPriorityMessage==
  UNION{LeaseRequestMessage,PathRequestMessage,PathRecallMessage}

(*Defn*)ServerInterlockMessageSet==SUBSET ServerInterlockMessage

ASSUME ServerMessage \subseteq Blob
====
