---- MODULE ClientKnowledgePredicatesModule ----
(*`^\addcontentsline{toc}{section}{ClientKnowledgePredicatesModule}^'*)

EXTENDS ClientPermissionPredicatesModule
(* ********** Label predicates ********************************************************************************************* *)

(*Defn*)KnowChildFile(fileID,label,childFile)==
  /\ MayUseReadOrWriteChildLease(fileID,label)
  /\ FileValueTableState[fileID].children[label]=childFile

(*Defn*)KnowParentFile(fileID,label,parentFile)==
  /\ MayUseReadOrWriteSVLease(fileID,FParent)
  /\ FileValueTableState[fileID].parent.fileID=parentFile
  /\ FileValueTableState[fileID].parent.label=label

(*Defn*)KnowLabelIsIndeterminate(fileID,label)==
  \E childFile \in FileID,childLabel \in NilOr(Label),parentFile \in NilOr(FileID)
     :
     /\ KnowChildFile(fileID,label,childFile)
     /\ KnowParentFile(childFile,childLabel,parentFile)
     /\ ( \/ parentFile#fileID
          \/ childLabel#label)

(*Defn*)KnowLabelIsUsed(fileID,label)==
  \E childFile \in FileID:KnowChildFile(fileID,label,childFile)

(*Defn*)KnowLabelIsUnused(fileID,label)==KnowChildFile(fileID,label,Nil)

(*Defn*)KnowFileHasChildren(fileID)==
  \E label \in Label:KnowLabelIsUsed(fileID,label)

(*Defn*)KnowFileHasNoChildren(fileID)==
  \A label \in Label:KnowLabelIsUnused(fileID,label)

(* ********** Path predicates ********************************************************************************************** *)

(*Defn*)KnowPrefixOfLabelPathConnectsFilePath(labelPath,filePath)==
  \A i \in 1..(Len(filePath)-1):
     /\ filePath[i]#Nil
     /\ KnowChildFile(filePath[i],labelPath[i],filePath[(i+1)])
     /\ KnowParentFile(filePath[(i+1)],labelPath[i],filePath[i])

(*Defn*)KnowPathResolvesToTarget(rootFile,labelPath,targetFile)==
  \E filePath \in FileSeq:
     /\ Len(filePath)=Len(labelPath)+1
     /\ rootFile=First(filePath)
     /\ targetFile=Last(filePath)
     /\ KnowPrefixOfLabelPathConnectsFilePath(labelPath,filePath)

(*Defn*)KnowPathDoesNotResolve(rootFile,labelPath)==
  \E filePath \in FileSeq:
     LET
       (*Defn*)n==Len(filePath)
       (*Defn*)lastFile==filePath[n]
       (*Defn*)lastLabel==labelPath[n]
     IN
       /\ filePath#<<>>
       /\ Len(filePath)\leq Len(labelPath)
       /\ rootFile=First(filePath)
       /\ KnowPrefixOfLabelPathConnectsFilePath(labelPath,filePath)
       /\ ( \/ KnowLabelIsUnused(lastFile,lastLabel)
            \/ KnowLabelIsIndeterminate(lastFile,lastLabel))

(*Defn*)KnowFileHasPartialFilePath(fileID,filePath)==
  \E labelPath \in LabelSeq:
     /\ Len(filePath)=Len(labelPath)+1
     /\ fileID=Last(filePath)
     /\ KnowPrefixOfLabelPathConnectsFilePath(labelPath,filePath)

(*Defn*)KnowFileHasFullFilePath(fileID,filePath)==
  /\ FilesystemRoot=First(filePath)
  /\ KnowFileHasPartialFilePath(fileID,filePath)

(*Defn*)KnowFileHasWarrantiedAncestorPath(fileID,ancestors)==
  /\ MayUsePathWarrant(fileID)
  /\ FileValueTableState[fileID].path=ancestors

(* ********** DelDisp predicates ******************************************************************************************* *)

(*Defn*)KnowFileDeletePending(fileID)==
  /\ MayUseReadOrWriteSVLease(fileID,FDelDisp)
  /\ FileValueTableState[fileID].delDisp=TRUE

(*Defn*)KnowFileNotDeletePending(fileID)==
  /\ MayUseReadOrWriteSVLease(fileID,FDelDisp)
  /\ FileValueTableState[fileID].delDisp=FALSE

(* ********** OpenHandle predicates **************************************************************************************** *)

(*Defn*)KnowFileOpenedByAnotherClient(fileID)==
  /\ MayUseOpenHandleLease(fileID,BBOther,PRead)
  /\ FileValueTableState[fileID].openHandle.other[thisHost]=TRUE

(*Defn*)KnowFileNotOpenedByAnotherClient(fileID)==
  /\ MayUseOpenHandleLease(fileID,BBOther,PRead)
  /\ FileValueTableState[fileID].openHandle.other[thisHost]=FALSE

(*Defn*)KnowHandleOpenOnFile(handle,fileID)==
  /\ MayUseOpenHandleLease(fileID,BBSelf,PRead)
  /\ handle \in FileValueTableState[fileID].openHandle.self[thisHost]
  /\ (\neg HandleOpeningSuspended(handle))

(*Defn*)KnowHandleNotOpenOnFile(handle,fileID)==
  /\ handle \notin FileValueTableState[fileID].openHandle.self[thisHost]
  /\ (\neg HandleClosingSuspended(handle))

(*Defn*)KnowSomeHandleOpenOnFile(fileID)==
  \E handle \in Handle:KnowHandleOpenOnFile(handle,fileID)

(*Defn*)KnowNoHandleOpenOnFile(fileID)==
  \A handle \in Handle:KnowHandleNotOpenOnFile(handle,fileID)

(*Defn*)KnowAnotherHandleOpenOnFile(handle,fileID)==
  \E otherHandle \in Handle:
     /\ otherHandle#handle
     /\ KnowHandleOpenOnFile(otherHandle,fileID)

(*Defn*)KnowNoOtherHandleOpenOnFile(handle,fileID)==
  \A otherHandle \in Handle:
     otherHandle#handle=>KnowHandleNotOpenOnFile(otherHandle,fileID)

(*Defn*)KnowCanOpenOrCloseFile(fileID)==
  /\ MayUseOpenHandleLease(fileID,BBSelf,PRead)
  /\ MayUseOpenHandleLease(fileID,BBSelf,PWrite)

(* ********** Bona fide predicates ***************************************************************************************** *)

(*Defn*)KnowHandleOnFileIsBonaFide(handle,fileID)==
  /\ MayUseBonaFideLease(fileID)
  /\ handle \in FileValueTableState[fileID].bonaFide[thisHost]
  /\ (\neg HandleOpeningSuspended(handle))

(*Defn*)KnowHandleOnFileNotBonaFide(handle,fileID)==
  /\ handle \notin FileValueTableState[fileID].bonaFide[thisHost]
  /\ (\neg HandleCleanupSuspended(handle))

(* ********** Mode predicates ********************************************************************************************** *)

(*Defn*)KnowHandleHasModeOnFile(handle,mode,fileID)==
  /\ KnowHandleOnFileIsBonaFide(handle,fileID)
  /\ handle \in FileValueTableState[fileID].modes[mode].self[thisHost]
  /\ (\neg HandleOpeningSuspended(handle))

(*Defn*)KnowHandleLacksModeOnFile(handle,mode,fileID)==
  /\ handle \notin FileValueTableState[fileID].modes[mode].self[thisHost]
  /\ (\neg HandleCleanupSuspended(handle))

(*Defn*)KnowSomeHandleHasModeOnFile(mode,fileID)==
  \E handle \in Handle:KnowHandleHasModeOnFile(handle,mode,fileID)

(*Defn*)KnowNoHandleHasModeOnFile(mode,fileID)==
  \A handle \in Handle:KnowHandleLacksModeOnFile(handle,mode,fileID)

(*Defn*)KnowAnotherHandleHasModeOnFile(handle,mode,fileID)==
  \E otherHandle \in Handle:
     /\ otherHandle#handle
     /\ KnowHandleHasModeOnFile(otherHandle,mode,fileID)

(*Defn*)KnowNoOtherHandleHasModeOnFile(handle,mode,fileID)==
  \A otherHandle \in Handle:
     otherHandle#handle=>KnowHandleLacksModeOnFile(otherHandle,mode,fileID)

(*Defn*)KnowModeSetConflicts(fileID,modes)==
  \E mode \in modes:
     \/ ( /\ MayUseModeLease(fileID,ModeOpposite(mode),BBOther)
          /\ FileValueTableState[fileID].modes[ModeOpposite(mode)].other[thisHost])
     \/ ( \E handle \in Handle:KnowHandleHasModeOnFile(handle,ModeOpposite(mode),fileID))

(* In the following predicate, there is no need to check the other value for
	the opposite modes, because the server will not grant writeSelf on a mode
	for which the other value is TRUE. *)

(*Defn*)KnowModeSetCompatible(fileID,modes)==
  \A mode \in modes,handle \in Handle:
     KnowHandleLacksModeOnFile(handle,ModeOpposite(mode),fileID)

(*Defn*)KnowCanSetOrClearFileMode(fileID,mode)==
  MayUseModeLease(fileID,mode,BBSelf)

(* ********** Access predicates ******************************************************************************************** *)

(*Defn*)KnowHandleHasAccessToFile(handle,access,fileID)==
  /\ KnowHandleOpenOnFile(handle,fileID)
  /\ handle \in(FileValueTableState[fileID].accesses[access])[thisHost]
  /\ (\neg HandleOpeningSuspended(handle))

(*Defn*)KnowHandleLacksAccessToFile(handle,access,fileID)==
  /\ handle \notin(FileValueTableState[fileID].accesses[access])[thisHost]
  /\ (\neg HandleClosingSuspended(handle))

(* ********** ClientLog predicates ***************************************************************************************** *)

(*Defn*)KnowFileCreationInProgress(fileID)==
  \E index \in DOMAIN MessageLog:
     /\ MessageLog[index].msg \in CreateFileOperationMessage
     /\ MessageLog[index].sentTo=Nil
     /\ MessageLog[index].msg.fileID=fileID

(*Defn*)KnowHandleClosingNotInProgress(handle)==
  \A index \in DOMAIN MessageLog:
     MessageLog[index].msg \in
     CloseFileOperationMessage \union CloseAndUnlinkFileOperationMessage
     =>
     MessageLog[index].msg.handle#handle
====
