---- MODULE ThreadModule ----
(*`^\addcontentsline{toc}{section}{ThreadModule}^'*)

EXTENDS APIComponentsModule,ModeModule,PriorityModule
(* 
	This module defines the variable ThreadTable, which is a table of records
	containing information about threads.  Each record indicates three things:
	(1) whether the thread is performing computation or blocked waiting for a
	reply from the filesystem, (2) the most recent request submitted to the
	filesystem, and (3) the most recent reply returned by the filesystem.

	Each request includes one of seven supported commands, a handle on which to
	perform the command, and additional command-specific information.  Each
	reply includes a return code and a command-specific return value.  These
	structures are defined before the declaration of ThreadTable.

	The filesystem receives a request by blocking the thread and recording the
	submitted request.  The filesystem returns a reply by recording the result
	and unblocking the thread.  Operators to support these actions are defined
	after the declaration of ThreadTable.
 *)

(* ********** Requests ***************************************************************************************************** *)

(*Defn*)CmdOpen=="CmdOpen"
(*Defn*)CmdCleanup=="CmdCleanup"
(*Defn*)CmdClose=="CmdClose"
(*Defn*)CmdRead=="CmdRead"
(*Defn*)CmdWrite=="CmdWrite"
(*Defn*)CmdCreate=="CmdCreate"
(*Defn*)CmdOpenOrCreate=="CmdOpenOrCreate"
(*Defn*)CmdDelete=="CmdDelete"
(*Defn*)CmdMove=="CmdMove"
(*Defn*)CmdAuxStatsTrigger=="CmdAuxStatsTrigger"
(*Defn*)Command==
  {
  CmdOpen,
  CmdCleanup,
  CmdClose,
  CmdRead,
  CmdWrite,
  CmdCreate,
  CmdOpenOrCreate,
  CmdDelete,
  CmdMove,
  CmdAuxStatsTrigger
  }

(*Defn*)OpenRequest==
  [cmd:{CmdOpen},priority:Priority,handle:Handle,path:LabelSeq,modeSet:ModeSet]
(*Defn*)MakeOpenRequest(i_priority,i_handle,i_path,i_modeSet)==
  [cmd|->CmdOpen,handle|->i_handle,path|->i_path,modeSet|->i_modeSet]

(*Defn*)CloseRequest==[cmd:{CmdClose},priority:Priority,handle:Handle]
(*Defn*)MakeCloseRequest(i_priority,i_handle)==
  [cmd|->CmdClose,handle|->i_handle]

(*Defn*)CleanupRequest==[cmd:{CmdCleanup},priority:Priority,handle:Handle]
(*Defn*)MakeCleanupRequest(i_priority,i_handle)==
  [cmd|->CmdCleanup,handle|->i_handle]

(*Defn*)ReadRequest==[cmd:{CmdRead},priority:Priority,handle:Handle]
(*Defn*)MakeReadRequest(i_priority,i_handle)==
  [cmd|->CmdRead,handle|->i_handle]

(*Defn*)WriteRequest==
  [cmd:{CmdWrite},priority:Priority,handle:Handle,content:Content]
(*Defn*)MakeWriteRequest(i_priority,i_handle,i_content)==
  [cmd|->CmdWrite,handle|->i_handle,content|->i_content]

(*Defn*)CreateRequest==
  [
  cmd:{CmdCreate},priority:Priority,handle:Handle,path:LabelSeq,modeSet:ModeSet
  ]
(*Defn*)MakeCreateRequest(i_priority,i_handle,i_path,i_modeSet)==
  [cmd|->CmdCreate,handle|->i_handle,path|->i_path,modeSet|->i_modeSet]

(*Defn*)OpenOrCreateRequest==
  [
    cmd:{CmdOpenOrCreate},
    priority:Priority,
    handle:Handle,
    path:LabelSeq,
    modeSet:ModeSet
  ]
(*Defn*)MakeOpenOrCreateRequest(i_priority,i_handle,i_path,i_modeSet)==
  [cmd|->CmdOpenOrCreate,handle|->i_handle,path|->i_path,modeSet|->i_modeSet]

(*Defn*)DeleteRequest==
  [cmd:{CmdDelete},priority:Priority,handle:Handle,delDisp:Boolean]
(*Defn*)MakeDeleteRequest(i_priority,i_handle,i_delDisp)==
  [cmd|->CmdDelete,handle|->i_handle,delDisp|->i_delDisp]

(*Defn*)MoveRequest==
  [
    cmd:{CmdMove},
    priority:Priority,
    childHandle:Handle,
    destRootHandle:Handle,
    destPath:LabelSeq
  ]
(*Defn*)
MakeMoveRequest(i_priority,i_childHandle,i_destRootHandle,i_destPath)==
  [
  cmd|->CmdMove,
  childHandle|->i_childHandle,
  destRootHandle|->i_destRootHandle,
  destPath|->i_destPath
  ]

(*Defn*)AuxStatsTriggerRequest==
  [cmd:{CmdAuxStatsTrigger},priority:Priority,label:Label]
(*Defn*)MakeAuxStatsTriggerRequest(i_priority,i_label)==
  [cmd|->CmdAuxStatsTrigger,label|->i_label]
(*Defn*)Request==
  UNION
  {
  OpenRequest,
  CloseRequest,
  CleanupRequest,
  ReadRequest,
  WriteRequest,
  CreateRequest,
  OpenOrCreateRequest,
  DeleteRequest,
  MoveRequest,
  AuxStatsTriggerRequest
  }
(*Defn*)Request_debugPrint(this)=={}

(*Defn*)TaggedRequest==[tag:Nat,request:Request]
(*Defn*)MakeTaggedRequest(i_tag,i_request)==[tag|->i_tag,request|->i_request]

(*Defn*)RequestInit==CHOOSE request \in Request:TRUE

(*  TLC hack version  *)

(* 
<Definition>RequestInit == Nil</Definition>
 *)

(* ********** Replies ****************************************************************************************************** *)

(* 
<Enum name="ReturnValueType">
	<Enum-Value name="RVContent"/>
	<Enum-Value name="RVHandle"/>
	<Enum-Value name="RVNil"/>
</Enum>
<Struct set="ReturnValue" encodable="true">
	<Struct-Field name="type" type="ReturnValueType" isKeyField="true" />
	<Struct set="ReturnValueContent" keyValue="RVContent">
		<Struct-Field name="content" type="Content" />
	</Struct>
	<Struct set="ReturnValueHandle" keyValue="RVHandle">
		<Struct-Field name="handle" type="Handle" />
	</Struct>
	<Struct set="ReturnValueNil" keyValue="RVNil">
		<Struct-Field name="handle" type="Handle" />
	</Struct>
</Struct>
 *)

(*Defn*)RCSuccess=="RCSuccess"
(*Defn*)RCErrorArbitrary=="RCErrorArbitrary"
(*Defn*)RCErrorFileAlreadyExists=="RCErrorFileAlreadyExists"
(*Defn*)RCErrorPathNotFound=="RCErrorPathNotFound"
(*Defn*)RCErrorSharingViolation=="RCErrorSharingViolation"
(*Defn*)ResultCode==
  {
  RCSuccess,
  RCErrorArbitrary,
  RCErrorFileAlreadyExists,
  RCErrorPathNotFound,
  RCErrorSharingViolation
  }

(*Defn*)ReturnValueType_Content=="ReturnValueType_Content"
(*Defn*)ReturnValueType_Handle=="ReturnValueType_Handle"
(*Defn*)ReturnValueType_Nil=="ReturnValueType_Nil"
(*Defn*)ReturnValueType==
  {ReturnValueType_Content,ReturnValueType_Handle,ReturnValueType_Nil}

(*Defn*)ReturnValueContent==Content
(*Defn*)ReturnValueHandle==Handle
(*Defn*)ReturnValueNil=={Nil}
(*Defn*)ReturnValue==
  UNION{ReturnValueContent,ReturnValueHandle,ReturnValueNil}

(*Defn*)Reply==[rc:ResultCode,value:ReturnValue]
(*Defn*)MakeReply(i_rc,i_value)==[rc|->i_rc,value|->i_value]

(*Defn*)TaggedReply==[tag:Nat,reply:Reply]
(*Defn*)MakeTaggedReply(i_tag,i_reply)==[tag|->i_tag,reply|->i_reply]

(*Defn*)ReplyInit==CHOOSE reply \in Reply:TRUE

(* ********** ThreadInfo *************************************************************************************************** *)

(*Defn*)ThreadInfo==[blocked:Boolean,request:Request,reply:Reply]

(*Defn*)ThreadInfoInit==
  [blocked|->FALSE,request|->RequestInit,reply|->ReplyInit]

(* ********** ThreadTable ************************************************************************************************** *)

(*Defn*)ThreadTableType==[Thread->ThreadInfo]

(*Defn*)ThreadTableInit==[thread \in Thread|->ThreadInfoInit]

VARIABLE ThreadTable

(* ********** Predicates *************************************************************************************************** *)

(*Defn*)IsRequestReady(thread,request)==
  /\ ThreadTable[thread].blocked
  /\ ThreadTable[thread].request=request

(* ********** Partial Actions ********************************************************************************************** *)

(*Defn*)ThreadReturn(thread,reply)==
  /\ ThreadTable[thread].blocked
  /\ (ThreadTable')=
     [ThreadTable EXCEPT![thread]=[@EXCEPT!.reply=reply,!.blocked=FALSE]]

(*Defn*)ThreadNoReturn==UNCHANGED ThreadTable

(* ********** Actions ****************************************************************************************************** *)

(*Defn*)ReceiveOperationRequest==
  \E thread \in Thread,req \in Request:
     /\ (\neg ThreadTable[thread].blocked)
     /\ (ThreadTable')=
        [ThreadTable EXCEPT![thread]=[@EXCEPT!.request=req,!.blocked=TRUE]]
====
