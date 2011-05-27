---- MODULE ServerKnowledgePredicatesModule ----
(*`^\addcontentsline{toc}{section}{ServerKnowledgePredicatesModule}^'*)

EXTENDS ServerLeasePredicatesModule
(* ********** Label predicates ********************************************************************************************* *)

(*Defn*)KnowChildFile(fileID,label,childFile)==
  /\ (\A client \in Client:(\neg ClientHasWriteChildLease(client,fileID,label)))
  /\ FileValueTableState[fileID].children[label]=childFile

(*Defn*)KnowParentFile(fileID,label,parentFile)==
  /\ (\A client \in Client:(\neg ClientHasWriteSVLease(client,fileID,FParent)))
  /\ FileValueTableState[fileID].parent=MakeParent(parentFile,label)

(*Defn*)KnowLabelIsUsed(fileID,label)==
  \E childFile \in FileID:KnowChildFile(fileID,label,childFile)

(*Defn*)KnowLabelIsUnused(fileID,label)==KnowChildFile(fileID,label,Nil)

(*Defn*)KnowFileHasChildren(fileID)==
  \E label \in Label:KnowLabelIsUsed(fileID,label)

(*Defn*)KnowFileHasNoChildren(fileID)==
  \A label \in Label:KnowLabelIsUnused(fileID,label)

(* ********** DelDisp predicates ******************************************************************************************* *)

(*Defn*)KnowFileDeletePending(fileID)==
  /\ (\A client \in Client:(\neg ClientHasWriteSVLease(client,fileID,FDelDisp)))
  /\ FileValueTableState[fileID].delDisp=TRUE

(*Defn*)KnowFileNotDeletePending(fileID)==
  /\ (\A client \in Client:(\neg ClientHasWriteSVLease(client,fileID,FDelDisp)))
  /\ FileValueTableState[fileID].delDisp=FALSE

(* ********** Open Handle predicates ************************************************************************************** *)

(*Defn*)KnowClientHasFileOpen(client,fileID)==
  ClientHasHeldOpenHandleValue(client,fileID,TRUE)

(*Defn*)KnowClientHasNotFileOpen(client,fileID)==
  ClientHasHeldOpenHandleValue(client,fileID,FALSE)

(*Defn*)KnowAnotherClientHasFileOpen(client,fileID)==
  \E otherClient \in Client:
     /\ otherClient#client
     /\ KnowClientHasFileOpen(otherClient,fileID)

(*Defn*)KnowNoOtherClientHasFileOpen(client,fileID)==
  \A otherClient \in Client:
     otherClient#client=>KnowClientHasNotFileOpen(otherClient,fileID)

(* ********** Mode predicates ********************************************************************************************** *)

(*Defn*)KnowClientHasFileMode(client,fileID,mode)==
  ClientHasHeldModeValue(client,fileID,mode,TRUE)

(*Defn*)KnowClientHasNotFileMode(client,fileID,mode)==
  ClientHasHeldModeValue(client,fileID,mode,FALSE)

(*Defn*)KnowAnotherClientHasFileMode(client,fileID,mode)==
  \E otherClient \in Client:
     /\ otherClient#client
     /\ KnowClientHasFileMode(otherClient,fileID,mode)

(*Defn*)KnowAllOtherClientsHaveCompatibleModeSets(client,fileID,modes)==
  \A mode \in modes,otherClient \in Client:
     otherClient#client=>
     KnowClientHasNotFileMode(otherClient,fileID,ModeOpposite(mode))
====
