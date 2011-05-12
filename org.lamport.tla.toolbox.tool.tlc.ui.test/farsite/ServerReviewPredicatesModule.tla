---- MODULE ServerReviewPredicatesModule ----
(*`^\addcontentsline{toc}{section}{ServerReviewPredicatesModule}^'*)

EXTENDS ServerLeasePredicatesModule
(* The predicates in this fileID all have past-tense names to reflect the fact
	that they refer to a state of the client in the past, particularly at the
	point in the update sequence that the server is processing.
 *)

(* ********** Label predicates ********************************************************************************************* *)

(*Defn*)ClientKnewChildFile(client,parentFile,label,childFile)==
  /\ ClientHasReadOrWriteChildLease(client,parentFile,label)
  /\ FileValueTableState[parentFile].children[label]=childFile

(*Defn*)ClientKnewParentFile(client,childFile,label,parentFile)==
  /\ ClientHasReadOrWriteSVLease(client,childFile,FParent)
  /\ FileValueTableState[childFile].parent=MakeParent(parentFile,label)

(*Defn*)ClientKnewLabelWasUnused(client,fileID,label)==
  ClientKnewChildFile(client,fileID,label,Nil)

(*Defn*)ClientKnewFileHadNoChildren(client,fileID)==
  \A label \in Label:ClientKnewLabelWasUnused(client,fileID,label)

(* ********** Path predicates ********************************************************************************************** *)

(*Defn*)ClientKnewFileHadWarrantiedAncestorPath(client,fileID,ancestors)==
  /\ ClientHasPathWarrant(client,fileID)
  /\ FileValueTableState[fileID].path=ancestors

(* ********** DelDisp predicates ******************************************************************************************* *)

(*Defn*)ClientKnewFileDeletePending(client,fileID)==
  /\ ClientHasReadOrWriteSVLease(client,fileID,FDelDisp)
  /\ FileValueTableState[fileID].delDisp=TRUE

(*Defn*)ClientKnewFileNotDeletePending(client,fileID)==
  /\ ClientHasReadOrWriteSVLease(client,fileID,FDelDisp)
  /\ FileValueTableState[fileID].delDisp=FALSE

(* ********** OpenHandle predicates **************************************************************************************** *)

(*Defn*)ClientKnewFileOpenedByAnotherClient(client,fileID)==
  /\ ClientHasOpenHandleLease(client,fileID,BBOther,PRead)
  /\ FileValueTableState[fileID].openHandle.other[client]=TRUE

(*Defn*)ClientKnewFileNotOpenedByAnotherClient(client,fileID)==
  /\ ClientHasOpenHandleLease(client,fileID,BBOther,PRead)
  /\ FileValueTableState[fileID].openHandle.other[client]=FALSE

(*Defn*)ClientKnewHandleOpenOnFile(client,handle,fileID)==
  /\ ClientHasOpenHandleLease(client,fileID,BBSelf,PRead)
  /\ handle \in FileValueTableState[fileID].openHandle.self[client]

(*Defn*)ClientKnewHandleNotOpenOnFile(client,handle,fileID)==
  handle \notin FileValueTableState[fileID].openHandle.self[client]

(*Defn*)ClientKnewSomeHandleOpenOnFile(client,fileID)==
  \E handle \in Handle:ClientKnewHandleOpenOnFile(client,handle,fileID)

(*Defn*)ClientKnewNoHandleOpenOnFile(client,fileID)==
  \A handle \in Handle:ClientKnewHandleNotOpenOnFile(client,handle,fileID)

(*Defn*)ClientKnewAnotherHandleOpenOnFile(client,handle,fileID)==
  \E otherHandle \in Handle:
     /\ otherHandle#handle
     /\ ClientKnewHandleOpenOnFile(client,otherHandle,fileID)

(*Defn*)ClientKnewNoOtherHandleOpenOnFile(client,handle,fileID)==
  \A otherHandle \in Handle:
     otherHandle#handle=>ClientKnewHandleNotOpenOnFile(client,otherHandle,fileID)

(*Defn*)ClientKnewCouldOpenOrCloseFile(client,fileID)==
  /\ ClientHasOpenHandleLease(client,fileID,BBSelf,PRead)
  /\ ClientHasOpenHandleLease(client,fileID,BBSelf,PWrite)

(* ********** Bona fide predicates ***************************************************************************************** *)

(*Defn*)ClientKnewHandleOnFileWasBonaFide(client,handle,fileID)==
  /\ ClientHasBonaFideLease(client,fileID)
  /\ handle \in FileValueTableState[fileID].bonaFide[client]

(*Defn*)ClientKnewHandleOnFileNotBonaFide(client,handle,fileID)==
  handle \notin FileValueTableState[fileID].bonaFide[client]

(* ********** Mode predicates ********************************************************************************************** *)

(*Defn*)ClientKnewHandleHadModeOnFile(client,handle,mode,fileID)==
  /\ ClientKnewHandleOnFileWasBonaFide(client,handle,fileID)
  /\ handle \in FileValueTableState[fileID].modes[mode].self[client]

(*Defn*)ClientKnewHandleLackedModeOnFile(client,handle,mode,fileID)==
  handle \notin FileValueTableState[fileID].modes[mode].self[client]

(*Defn*)ClientKnewSomeHandleHadModeOnFile(client,mode,fileID)==
  \E handle \in Handle:ClientKnewHandleHadModeOnFile(mode,handle,mode,fileID)

(*Defn*)ClientKnewNoHandleHadModeOnFile(client,mode,fileID)==
  \A handle \in Handle:ClientKnewHandleLackedModeOnFile(client,handle,mode,fileID)

(*Defn*)ClientKnewAnotherHandleHadModeOnFile(client,handle,mode,fileID)==
  \E otherHandle \in Handle:
     /\ otherHandle#handle
     /\ ClientKnewHandleHadModeOnFile(client,otherHandle,mode,fileID)

(*Defn*)ClientKnewNoOtherHandleHadModeOnFile(client,handle,mode,fileID)==
  \A otherHandle \in Handle:
     otherHandle#handle=>
     ClientKnewHandleLackedModeOnFile(client,otherHandle,mode,fileID)

(*Defn*)ClientKnewModeSetCompatible(client,fileID,modes)==
  \A mode \in modes,handle \in Handle:
     ClientKnewHandleLackedModeOnFile(client,handle,ModeOpposite(mode),fileID)

(*Defn*)ClientKnewCouldSetOrClearFileMode(client,fileID,mode)==
  ClientHasModeLease(client,fileID,mode,BBSelf)

(* ********** Access predicates ******************************************************************************************** *)

(*Defn*)ClientKnewHandleHadAccessToFile(client,handle,access,fileID)==
  /\ ClientKnewHandleOpenOnFile(client,handle,fileID)
  /\ handle \in(FileValueTableState[fileID].accesses[access])[client]

(*Defn*)ClientKnewHandleLackedAccessToFile(client,handle,access,fileID)==
  handle \notin(FileValueTableState[fileID].accesses[access])[client]
====
