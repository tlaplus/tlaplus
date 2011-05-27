---- MODULE ServerLeasePredicatesModule ----
(*`^\addcontentsline{toc}{section}{ServerLeasePredicatesModule}^'*)

EXTENDS ServerFileProtectionModule
(* ********** Lease predicates for lease management ************************************************************************ *)

(*Defn*)SharedValueLeaseReserved(sharedValueLease)==
  sharedValueLease.reservation.leader#Nil

(*Defn*)ClientHasIndividualSVLease(client,sharedValueLease,rw)==
  \neg NowLaterThan((sharedValueLease.individual[client])[rw])

(*Defn*)ClientIndividualChildLeaseExpirationTime(client,fileID,label,rw)==
  IF
    /\ rw=PWrite
    /\ FileProtectionTableState[fileID].children.infinite.client=client
    /\ label \notin
       FileProtectionTableState[fileID].children.infinite.excludedLabels
  THEN
    FileProtectionTableState[fileID].children.infinite.write
  ELSE
    ( FileProtectionTableState[fileID].children.singleton[label].individual
      [
      client
      ])
    [
    rw
    ]

(*Defn*)ClientHasIndividualChildLease(client,fileID,label,rw)==
  \neg
  NowLaterThan(
    ClientIndividualChildLeaseExpirationTime(client,fileID,label,rw))

(*Defn*)ClientHasInfiniteChildLease(client,fileID)==
  /\ FileProtectionTableState[fileID].children.infinite.client=client
  /\ (\neg NowLaterThan(FileProtectionTableState[fileID].children.infinite.write))

(*Defn*)ClientHasInfiniteChildLeaseOnLabel(client,fileID,label)==
  /\ label \notin
     FileProtectionTableState[fileID].children.infinite.excludedLabels
  /\ FileProtectionTableState[fileID].children.infinite.client=client
  /\ (\neg NowLaterThan(FileProtectionTableState[fileID].children.infinite.write))

(*Defn*)ClientHasIndividualBBLease(client,blackBoxLease,so,rw)==
  \neg NowLaterThan((blackBoxLease[so].individual[client])[rw])

(*Defn*)ClientHasIndividualPVLease(client,privateValueLease)==
  \neg NowLaterThan(privateValueLease.individual[client].read)

(*Defn*)ClientHasPathWarrant(client,fileID)==
  \neg
  NowLaterThan(FileProtectionTableState[fileID].path.individual[client].read)

(*Defn*)DownPathLeaseIssued(fileID,label)==
  \neg NowLaterThan(FileProtectionTableState[fileID].path.down[label])

(*Defn*)UpPathLeaseObtained(fileID)==
  \neg NowLaterThan(FileProtectionTableState[fileID].path.up)

(*Defn*)UpPathLeaseConfirmed(fileID)==
  NowEarlierThan(FileProtectionTableState[fileID].path.up)

(*Defn*)ReturnedUpPathLease(fileID)==
  FileProtectionTableState[fileID].path.up=BeforeTimeBegins

(* ********** Lease predicates for state operations ************************************************************************ *)

(*Defn*)ClientHasReadSVLease(client,fileID,field)==
  \/ ClientHasIndividualSVLease(
       client,(FileProtectionTableState[fileID])[field],PRead)
  \/ (\neg NowLaterThan((FileProtectionTableState[fileID])[field].everyone.read))

(*Defn*)ClientHasWriteSVLease(client,fileID,field)==
  ClientHasIndividualSVLease(
    client,(FileProtectionTableState[fileID])[field],PWrite)

(*Defn*)ClientHasReadOrWriteSVLease(client,fileID,field)==
  \/ ClientHasReadSVLease(client,fileID,field)
  \/ ClientHasWriteSVLease(client,fileID,field)

(*Defn*)ClientHasReadChildLease(client,fileID,label)==
  \/ ClientHasIndividualChildLease(client,fileID,label,PRead)
  \/ ( \neg
       NowLaterThan(
         FileProtectionTableState[fileID].children.singleton[label].everyone.read))

(*Defn*)ClientHasWriteChildLease(client,fileID,label)==
  ClientHasIndividualChildLease(client,fileID,label,PWrite)

(*Defn*)ClientHasReadOrWriteChildLease(client,fileID,label)==
  \/ ClientHasReadChildLease(client,fileID,label)
  \/ ClientHasWriteChildLease(client,fileID,label)

(*Defn*)ClientHasOpenHandleLease(client,fileID,so,rw)==
  \/ ClientHasIndividualBBLease(
       client,FileProtectionTableState[fileID].openHandle,so,rw)
  \/ ( \neg
       NowLaterThan(FileProtectionTableState[fileID].openHandle[so].everyone[rw]))

(*Defn*)ClientHasBonaFideLease(client,fileID)==
  \/ ClientHasIndividualPVLease(client,FileProtectionTableState[fileID].bonaFide)
  \/ (\neg NowLaterThan(FileProtectionTableState[fileID].bonaFide.everyone.read))

(*Defn*)ClientHasModeLease(client,fileID,mode,so)==
  LET
    (*Defn*)rw==IF so=BBSelf THEN PWrite ELSE PRead
  IN
    \/ ClientHasIndividualBBLease(
         client,FileProtectionTableState[fileID].modes[mode],so,rw)
    \/ ( \neg
         NowLaterThan(
           (FileProtectionTableState[fileID].modes[mode])[so].everyone[rw]))

(* ********** Additional lease predicates for black-box lease management *************************************************** *)

(*Defn*)CanSpontaneouslyCleanupClientHandleOnFile(client,handle,fileID)==
  /\ handle \in FileValueTableState[fileID].openHandle.self[client]
  /\ handle \in FileValueTableState[fileID].bonaFide[client]
  /\ (\neg ClientHasBonaFideLease(client,fileID))

(*Defn*)CanSpontaneouslyCloseClientHandleOnFile(client,handle,fileID)==
  /\ handle \in FileValueTableState[fileID].openHandle.self[client]
  /\ handle \notin FileValueTableState[fileID].bonaFide[client]
  /\ (\neg ClientHasOpenHandleLease(client,fileID,BBSelf,PRead))

(*Defn*)ClientHasHeldOpenHandleValue(client,fileID,value)==
  /\ (\neg ClientHasOpenHandleLease(client,fileID,BBSelf,PWrite))
  /\ (FileValueTableState[fileID].openHandle.self[client]#{})=value

(*Defn*)ClientIgnoresOtherOpenHandles(client,fileID)==
  \neg ClientHasOpenHandleLease(client,fileID,BBOther,PRead)

(*Defn*)ClientShieldedFromOtherOpenHandles(client,fileID)==
  \E otherClient \in Client:
     /\ otherClient#client
     /\ ClientHasHeldOpenHandleValue(otherClient,fileID,TRUE)

(*Defn*)ClientOpenHandleHiddenFromOthers(client,fileID)==
  \A otherClient \in Client:
     otherClient#client=>
     \/ ClientIgnoresOtherOpenHandles(otherClient,fileID)
     \/ ClientShieldedFromOtherOpenHandles(otherClient,fileID)

(*Defn*)ClientHasHeldModeValue(client,fileID,mode,value)==
  /\ (\neg ClientHasModeLease(client,fileID,mode,BBSelf))
  /\ (FileValueTableState[fileID].modes[mode].self[client]#{})=value

(*Defn*)ClientIgnoresOtherModes(client,fileID,mode)==
  \neg ClientHasModeLease(client,fileID,mode,BBOther)

(*Defn*)ClientShieldedFromOtherModes(client,fileID,mode)==
  \E otherClient \in Client:
     /\ otherClient#client
     /\ ClientHasHeldModeValue(otherClient,fileID,mode,TRUE)

(*Defn*)ClientModeHiddenFromOthers(client,fileID,mode)==
  \A otherClient \in Client:
     otherClient#client=>
     \/ ClientIgnoresOtherModes(otherClient,fileID,mode)
     \/ ClientShieldedFromOtherModes(otherClient,fileID,mode)
====
