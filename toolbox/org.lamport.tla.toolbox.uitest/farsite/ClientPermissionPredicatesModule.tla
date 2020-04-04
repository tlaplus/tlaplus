---- MODULE ClientPermissionPredicatesModule ----
(*`^\addcontentsline{toc}{section}{ClientPermissionPredicatesModule}^'*)

EXTENDS ClientLogModule
(*Defn*)MayUseReadSVLease(fileID,field)==HaveReadSVLease(fileID,field)

(*Defn*)MayUseWriteSVLease(fileID,field)==
  /\ HaveWriteSVLease(fileID,field)
  /\ (\neg FileFieldSVLeaseSuspended(fileID,field))

(*Defn*)MayUseReadOrWriteSVLease(fileID,field)==
  \/ MayUseReadSVLease(fileID,field)
  \/ MayUseWriteSVLease(fileID,field)

(*Defn*)MayUseReadChildLease(fileID,label)==HaveReadChildLease(fileID,label)

(*Defn*)MayUseWriteChildLease(fileID,label)==
  /\ HaveWriteChildLease(fileID,label)
  /\ (\neg FileFieldChildLeaseSuspended(fileID,label))

(*Defn*)MayUseReadOrWriteChildLease(fileID,label)==
  \/ MayUseReadChildLease(fileID,label)
  \/ MayUseWriteChildLease(fileID,label)

(*Defn*)MayUseOpenHandleLease(fileID,so,rw)==
  HaveOpenHandleLease(fileID,so,rw)

(*Defn*)MayUseBonaFideLease(fileID)==HaveBonaFideLease(fileID)

(*Defn*)MayUseModeLease(fileID,mode,so)==HaveModeLease(fileID,mode,so)

(*Defn*)MayUsePathWarrant(fileID)==HavePathWarrant(fileID)
====
