---- MODULE ServerLeaseResourcesModule ----
(*`^\addcontentsline{toc}{section}{ServerLeaseResourcesModule}^'*)

EXTENDS ServerMessageBuffersModule
(*Defn*)SLRTRead=="SLRTRead"
(*Defn*)SLRTWrite=="SLRTWrite"
(*Defn*)SLRTUp=="SLRTUp"
(*Defn*)SLRTDown=="SLRTDown"
(*Defn*)ServerLeaseResourceType=={SLRTRead,SLRTWrite,SLRTUp,SLRTDown}

(*Defn*)ServerLeaseResource==[fileID:FileID,type:ServerLeaseResourceType]
(*Defn*)MakeServerLeaseResource(i_fileID,i_type)==
  [fileID|->i_fileID,type|->i_type]

(*Defn*)LeaseRequestMessageRequiresResource(msg,resource)==
  /\ resource.fileID=msg.fileID
  /\ IF
       msg \in
       UNION
       {
       ReadFileRequestMessage,
       ResolveLabelRequestMessage,
       IdentifyParentRequestMessage
       }
     THEN
       resource.type=SLRTWrite
     ELSE IF msg \in LinkChildRequestMessage
     THEN
       resource.type \in{SLRTRead,SLRTWrite,SLRTUp}
     ELSE
       resource.type \in{SLRTRead,SLRTWrite}

(*Defn*)LeaseRequestMessageConsumesResource(msg,resource)==
  /\ resource.fileID=msg.fileID
  /\ IF
       msg \in
       UNION
       {
       ReadFileRequestMessage,
       ResolveLabelRequestMessage,
       IdentifyParentRequestMessage
       }
     THEN
       resource.type=SLRTRead
     ELSE
       resource.type \in{SLRTRead,SLRTWrite}

(*Defn*)PathRequestMessageRequiresResource(msg,resource)==
  /\ resource.fileID=msg.destFile
  /\ resource.type \in{SLRTWrite,SLRTUp}

(*Defn*)PathRequestMessageConsumesResource(msg,resource)==
  /\ resource.fileID=msg.destFile
  /\ resource.type=SLRTDown

(*Defn*)PathRecallMessageRequiresResource(msg,resource)==
  /\ resource.fileID=msg.destFile
  /\ resource.type \in{SLRTRead,SLRTDown}

(*Defn*)PathRecallMessageConsumesResource(msg,resource)==
  /\ resource.fileID=msg.destFile
  /\ resource.type=SLRTUp

(*Defn*)ServerPriorityMessageRequiresResource(msg,resource)==
  \/ ( /\ msg \in LeaseRequestMessage
       /\ LeaseRequestMessageRequiresResource(msg,resource))
  \/ ( /\ msg \in PathRequestMessage
       /\ PathRequestMessageRequiresResource(msg,resource))
  \/ ( /\ msg \in PathRecallMessage
       /\ PathRecallMessageRequiresResource(msg,resource))

(*Defn*)ServerPriorityMessageConsumesResource(msg,resource)==
  \/ ( /\ msg \in LeaseRequestMessage
       /\ LeaseRequestMessageConsumesResource(msg,resource))
  \/ ( /\ msg \in PathRequestMessage
       /\ PathRequestMessageConsumesResource(msg,resource))
  \/ ( /\ msg \in PathRecallMessage
       /\ PathRecallMessageConsumesResource(msg,resource))

(*Defn*)ServerPriorityMessageInBuffer(msg)==
  IF msg \in LeaseRequestMessage
  THEN
    MessageInLeaseRequestBuffer(msg)
  ELSE
    MessageInServerInterlockBuffer(msg)

(*Defn*)SomeServerMessageHasPriorityOverMessage(msg)==
  \E spMsg \in ServerPriorityMessage,resource \in ServerLeaseResource:
     /\ spMsg#msg
     /\ ServerPriorityMessageInBuffer(spMsg)
     /\ spMsg.priority<msg.priority
     /\ ServerPriorityMessageRequiresResource(spMsg,resource)
     /\ ServerPriorityMessageConsumesResource(msg,resource)
====
