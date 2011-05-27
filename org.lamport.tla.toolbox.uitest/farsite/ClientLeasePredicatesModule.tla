---- MODULE ClientLeasePredicatesModule ----
(*`^\addcontentsline{toc}{section}{ClientLeasePredicatesModule}^'*)

EXTENDS ClientFileProtectionModule
(* ********** Lease predicates for lease management ************************************************************************ *)

(*Defn*)
IndividualExpirationTimeOfFileSingletonField(
  fileSingletonField,rw,serNum,time)==
  IF
    \A protectionRecord \in ActiveProtectionRecords:
       ( \neg
         IndividualProtectionRecordIsRelevant(
           protectionRecord,fileSingletonField,rw,serNum,time))
  THEN
    BeforeTimeBegins
  ELSE
    LET
      (*Defn*)relevantProtectionRecord==
        CHOOSE protectionRecord \in ActiveProtectionRecords:
          IndividualProtectionRecordIsRelevant(
            protectionRecord,fileSingletonField,rw,serNum,time)
    IN
      relevantProtectionRecord.individual.expiration

(*Defn*)
IndividualExpirationTimeOfFileSingletonFieldSet(
  fileSingletonFields,rw,serNum,time)==
  MinElement(
    {
    IndividualExpirationTimeOfFileSingletonField(
      fileSingletonField,rw,serNum,time)
    :
      fileSingletonField \in fileSingletonFields
    })

(*Defn*)HaveIndividualLeaseOnFileSingletonField(fileSingletonField,rw)==
  NowEarlierThan(
    IndividualExpirationTimeOfFileSingletonField(
      fileSingletonField,rw,ActionSerialNumber,LateClock))

(* ********** Lease predicates for state operations ************************************************************************ *)

(*Defn*)ProtectionRecordExpirationTime(protectionRecord)==
  MaxElement({protectionRecord[ie].expiration:ie \in PIndividualOrEveryone})

(*Defn*)
ExpirationTimeOfFileSingletonField(fileSingletonField,rw,serNum,time)==
  IF
    \A protectionRecord \in ActiveProtectionRecords:
       ( \neg
         ProtectionRecordIsRelevant(
           protectionRecord,fileSingletonField,rw,serNum,time))
  THEN
    BeforeTimeBegins
  ELSE
    LET
      (*Defn*)relevantProtectionRecord==
        CHOOSE protectionRecord \in ActiveProtectionRecords:
          ProtectionRecordIsRelevant(
            protectionRecord,fileSingletonField,rw,serNum,time)
    IN
      ProtectionRecordExpirationTime(relevantProtectionRecord)

(*Defn*)
WriteExpirationTimeOfFileSingletonFieldSet(fileSingletonFields,serNum,time)==
  MinElement(
    {ExpirationTimeOfFileSingletonField(fileSingletonField,PWrite,serNum,time):
      fileSingletonField \in fileSingletonFields
    })

(*Defn*)
ReadOrWriteExpirationTimeOfFileSingletonFieldSet(
  fileSingletonFields,serNum,time)==
  MinElement(
    {
    MaxElement(
      {
      ExpirationTimeOfFileSingletonField(fileSingletonField,PRead,serNum,time),
      ExpirationTimeOfFileSingletonField(fileSingletonField,PWrite,serNum,time)
      })
    :
      fileSingletonField \in fileSingletonFields
    })

(*Defn*)HaveLeaseOnFileSingletonField(fileSingletonField,rw)==
  NowEarlierThan(
    ExpirationTimeOfFileSingletonField(
      fileSingletonField,rw,ActionSerialNumber,LateClock))

(* ********** Detailed lease predicates for state operations *************************************************************** *)

(*Defn*)HaveReadSVLease(fileID,field)==
  HaveLeaseOnFileSingletonField(MakeFileSharedValueField(fileID,field),PRead)

(*Defn*)HaveWriteSVLease(fileID,field)==
  HaveLeaseOnFileSingletonField(MakeFileSharedValueField(fileID,field),PWrite)

(*Defn*)HaveReadOrWriteSVLease(fileID,field)==
  \/ HaveReadSVLease(fileID,field)
  \/ HaveWriteSVLease(fileID,field)

(*Defn*)HaveReadChildLease(fileID,label)==
  HaveLeaseOnFileSingletonField(MakeFileChildField(fileID,label),PRead)

(*Defn*)HaveWriteChildLease(fileID,label)==
  HaveLeaseOnFileSingletonField(MakeFileChildField(fileID,label),PWrite)

(*Defn*)HaveReadOrWriteChildLease(fileID,label)==
  \/ HaveReadChildLease(fileID,label)
  \/ HaveWriteChildLease(fileID,label)

(*Defn*)HaveOpenHandleLease(fileID,so,rw)==
  HaveLeaseOnFileSingletonField(MakeFileOpenHandleField(fileID,so),rw)

(*Defn*)HaveBonaFideLease(fileID)==
  HaveLeaseOnFileSingletonField(MakeFileBonaFideField(fileID),PRead)

(*Defn*)HaveModeLease(fileID,mode,so)==
  LET
    (*Defn*)rw==IF so=BBSelf THEN PWrite ELSE PRead
  IN
    HaveLeaseOnFileSingletonField(MakeFileModeField(fileID,mode,so),rw)

(*Defn*)HavePathWarrant(fileID)==
  HaveLeaseOnFileSingletonField(MakeFilePathField(fileID),PRead)
====
