---- MODULE ClientLeaseResourcesModule ----
(*`^\addcontentsline{toc}{section}{ClientLeaseResourcesModule}^'*)

EXTENDS
  ClientMessageBufferModule,ClientKnowledgePredicatesModule,ThreadModule

(*Defn*)ClientLeaseResource==[fileID:FileID,rw:PReadOrWrite]
(*Defn*)MakeClientLeaseResource(i_fileID,i_rw)==[fileID|->i_fileID,rw|->i_rw]

(*Defn*)HandleRequiresResource(handle,resource,rws)==
  /\ KnowHandleOpenOnFile(handle,resource.fileID)
  /\ KnowHandleOnFileIsBonaFide(handle,resource.fileID)
  /\ resource.rw \in rws

(*Defn*)HandleAndPathRequireResource(handle,path,resource,rws)==
  \E rootFile \in FileID,prefixPath \in LabelSeq:
     /\ KnowHandleOpenOnFile(handle,rootFile)
     /\ KnowHandleOnFileIsBonaFide(handle,rootFile)
     /\ DoesSeqPrefixSeq(prefixPath,path)
     /\ KnowPathResolvesToTarget(rootFile,prefixPath,resource.fileID)
     /\ IF prefixPath=path THEN resource.rw \in rws ELSE resource.rw=PRead

(*Defn*)ParentOfHandleRequiresResource(handle,resource,rws)==
  \E childFile \in FileID,label \in Label:
     /\ KnowHandleOpenOnFile(handle,childFile)
     /\ KnowHandleOnFileIsBonaFide(handle,childFile)
     /\ KnowParentFile(childFile,label,resource.fileID)
     /\ resource.rw \in rws

(*Defn*)AncestorOfHandleRequiresResource(handle,resource)==
  \E leafFile \in FileID,filePath \in FileSeq:
     /\ KnowHandleOpenOnFile(handle,leafFile)
     /\ KnowHandleOnFileIsBonaFide(handle,leafFile)
     /\ KnowFileHasPartialFilePath(leafFile,filePath)
     /\ resource.fileID=First(filePath)
     /\ resource.rw=PRead

(*Defn*)OperationRequestRequiresResource(req,resource)==
  \/ ( /\ req.cmd=CmdOpen
       /\ HandleAndPathRequireResource(req.handle,req.path,resource,{PRead,PWrite}))
  \/ ( /\ req.cmd=CmdCleanup
       /\ HandleRequiresResource(req.handle,resource,{PRead,PWrite}))
  \/ ( /\ req.cmd=CmdClose
       /\ HandleRequiresResource(req.handle,resource,{PRead,PWrite}))
  \/ ( /\ req.cmd=CmdRead
       /\ HandleRequiresResource(req.handle,resource,{PRead}))
  \/ ( /\ req.cmd=CmdWrite
       /\ HandleRequiresResource(req.handle,resource,{PRead,PWrite}))
  \/ ( /\ req.cmd=CmdCreate
       /\ HandleAndPathRequireResource(req.handle,req.path,resource,{PRead,PWrite}))
  \/ ( /\ req.cmd=CmdOpenOrCreate
       /\ HandleAndPathRequireResource(req.handle,req.path,resource,{PRead,PWrite}))
  \/ ( /\ req.cmd=CmdDelete
       /\ HandleRequiresResource(req.handle,resource,{PRead,PWrite}))
  \/ ( /\ req.cmd=CmdMove
       /\ ( \/ HandleRequiresResource(req.childHandle,resource,{PRead,PWrite})
            \/ ParentOfHandleRequiresResource(req.childHandle,resource,{PRead,PWrite})
            \/ HandleAndPathRequireResource(
                 req.destRootHandle,req.destPath,resource,{PRead,PWrite})
            \/ AncestorOfHandleRequiresResource(req.destRootHandle,resource)))

(*Defn*)LeaseRecallMessageConsumesResource(msg,resource)==
  /\ msg.fileField.fileID=resource.fileID
  /\ msg.rw=resource.rw

(*Defn*)SomeOperationHasPriorityOverLeaseRecallMessage(msg)==
  \E thread \in Thread,req \in Request,resource \in ClientLeaseResource:
     /\ IsRequestReady(thread,req)
     /\ req.priority<msg.priority
     /\ OperationRequestRequiresResource(req,resource)
     /\ LeaseRecallMessageConsumesResource(msg,resource)
====
