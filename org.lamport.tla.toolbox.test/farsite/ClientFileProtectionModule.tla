---- MODULE ClientFileProtectionModule ----
(*`^\addcontentsline{toc}{section}{ClientFileProtectionModule}^'*)

EXTENDS ClientActionSerializerModule
(* ********** ProtectionRange and ProtectionRecord Definitions ************************************************************* *)

(*Defn*)ProtectionRanges==
  [
    beginSerNum:ClosedActionSerialNumber,
    endSerNum:ClosedActionSerialNumber,
    expiration:ClosedTime
  ]

(*Defn*)ProtectionRecord==
  [
    fileField:FileField,
    rw:PReadOrWrite,
    individual:ProtectionRanges,
    everyone:ProtectionRanges
  ]

(*Defn*)ProtectionRecordSet==SUBSET ProtectionRecord

(*Defn*)ProtectionRangeProtoNever==
  [beginSerNum|->Infinity,endSerNum|->Infinity,expiration|->BeforeTimeBegins]

(*Defn*)ProtectionRangeProtoAlways==
  [beginSerNum|->0,endSerNum|->Infinity,expiration|->AfterTimeEnds]

(*Defn*)ProtectionRangeProtoExpiring(expiration)==
  [beginSerNum|->0,endSerNum|->Infinity,expiration|->AfterTimeEnds]

(*Defn*)ProtectionRecordProto(fileField,rw)==
  [
  fileField|->fileField,
  rw|->rw,
  individual|->ProtectionRangeProtoNever,
  everyone|->ProtectionRangeProtoNever
  ]

(*Defn*)ProtectionRecordReadIndividualAlways(fileField)==
  [
  fileField|->fileField,
  rw|->PRead,
  individual|->ProtectionRangeProtoAlways,
  everyone|->ProtectionRangeProtoNever
  ]

(*Defn*)ProtectionRecordForCreate(fileField,rw,expiration)==
  [
  fileField|->fileField,
  rw|->rw,
  individual|->ProtectionRangeProtoExpiring(expiration),
  everyone|->ProtectionRangeProtoNever
  ]

(* ********** Active ProtectionRecord ************************************************************************************* *)

VARIABLE ActiveProtectionRecords

(*Defn*)ActiveProtectionRecordsType==ProtectionRecordSet

(*Defn*)ActiveProtectionRecordsInit==
  {
  ProtectionRecordReadIndividualAlways(
    MakeFileOpenHandleField(FilesystemRoot,BBSelf)),
  ProtectionRecordReadIndividualAlways(MakeFileBonaFideField(FilesystemRoot)),
  ProtectionRecordReadIndividualAlways(MakeFilePathField(FilesystemRoot))
  }

(* ********** Singleton / Infinite Conversion Operators ******************************************************************** *)

(*Defn*)ProtectionRecordToSingletonProtectionRecordSet(protectionRecord)==
  IF protectionRecord.fileField \in FileSingletonField
  THEN
    {protectionRecord}
  ELSE
    {
    [protectionRecord EXCEPT
      !.fileField=MakeFileChildField(protectionRecord.fileField.fileID,label)
    ]
    :
      label \in Label \ protectionRecord.fileField.excludedLabels
    }

(* Convert a finite set of ProtectionRecord to a possibly infinite set of ProtectionRecord over singleton fields *)

(*Defn*)
ProtectionRecordSetToSingletonProtectionRecordSet(protectionRecords)==
  UNION
  {ProtectionRecordToSingletonProtectionRecordSet(protectionRecord):
    protectionRecord \in protectionRecords
  }

(* Convert a possibly infinite set of ProtectionRecord over singleton fields to a finite set of ProtectionRecord *)

(*Defn*)
SingletonProtectionRecordSetToProtectionRecordSet(
  singletonProtectionRecords)==
  CHOOSE protectionRecords \in ProtectionRecordSet:
    /\ IsFiniteSet(protectionRecords)
    /\ ProtectionRecordSetToSingletonProtectionRecordSet(protectionRecords)=
       singletonProtectionRecords
    /\ ( \A otherProtectionRecords \in ProtectionRecordSet:
            \/ ProtectionRecordSetToSingletonProtectionRecordSet(otherProtectionRecords)#
               singletonProtectionRecords
            \/ (\neg IsFiniteSet(otherProtectionRecords))
            \/ Cardinality(otherProtectionRecords)\geq Cardinality(protectionRecords))

(* ********** Predicates *************************************************************************************************** *)

(*Defn*)
IndividualProtectionRecordIsRelevant(
  protectionRecord,fileSingletonField,rw,serNum,time)==
  /\ fileSingletonField \in
     FileFieldToFileSingletonFieldSet(protectionRecord.fileField)
  /\ protectionRecord.rw=rw
  /\ protectionRecord.individual.beginSerNum \leq serNum
  /\ protectionRecord.individual.endSerNum \geq serNum
  /\ protectionRecord.individual.expiration>time

(*Defn*)
ProtectionRecordIsRelevant(
  protectionRecord,fileSingletonField,rw,serNum,time)==
  \E ie \in PIndividualOrEveryone:
     /\ fileSingletonField \in
        FileFieldToFileSingletonFieldSet(protectionRecord.fileField)
     /\ protectionRecord.rw=rw
     /\ protectionRecord[ie].beginSerNum \leq serNum
     /\ protectionRecord[ie].endSerNum \geq serNum
     /\ protectionRecord[ie].expiration>time

(* ********** Ancillary Operators ****************************************************************************************** *)

(*Defn*)
UpdatedProtectionRecordsAfterLeaseRelease(
  inputProtectionRecords,fileSingletonFields,rw)==
  LET
    (*Defn*)relevantProtectionRecords==
      {protectionRecord \in inputProtectionRecords:
        ( \E fileSingletonField \in fileSingletonFields:
             ProtectionRecordIsRelevant(
               protectionRecord,fileSingletonField,rw,ActionSerialNumber,LateClock))
      }
    (*Defn*)possiblyRelevantSingletonProtectionRecords==
      ProtectionRecordSetToSingletonProtectionRecordSet(relevantProtectionRecords)
    (*Defn*)relevantSingletonProtectionRecords==
      {singletonProtectionRecord \in possiblyRelevantSingletonProtectionRecords:
        ( \E fileSingletonField \in fileSingletonFields:
             singletonProtectionRecord.fileField=fileSingletonField)
      }
    (*Defn*)irrelevantSingletonProtectionRecords==
      possiblyRelevantSingletonProtectionRecords \
      relevantSingletonProtectionRecords
    (*Defn*)newSingletonProtectionRecords==
      {[singletonProtectionRecord EXCEPT!.individual.endSerNum=ActionSerialNumber]:
        singletonProtectionRecord \in relevantSingletonProtectionRecords
      }
    (*Defn*)updatedSingletonProtectionRecords==
      newSingletonProtectionRecords \union irrelevantSingletonProtectionRecords
    (*Defn*)updatedProtectionRecords==
      SingletonProtectionRecordSetToProtectionRecordSet(
        updatedSingletonProtectionRecords)
  IN
    (inputProtectionRecords \ relevantProtectionRecords)\union
    updatedProtectionRecords

(* ********** Partial Actions ********************************************************************************************** *)

(*Defn*)
UpdateProtectionRecordsWithLeaseGrant(fileSingletonFields,rw,ie,expiration)==
  LET
    (*Defn*)relevantProtectionRecords==
      {protectionRecord \in ActiveProtectionRecords:
        ( \E fileSingletonField \in fileSingletonFields:
             ProtectionRecordIsRelevant(
               protectionRecord,fileSingletonField,rw,ActionSerialNumber,LateClock))
      }
    (*Defn*)possiblyRelevantSingletonProtectionRecords==
      ProtectionRecordSetToSingletonProtectionRecordSet(relevantProtectionRecords)
    (*Defn*)relevantSingletonProtectionRecords==
      {singletonProtectionRecord \in possiblyRelevantSingletonProtectionRecords:
        ( \E fileSingletonField \in fileSingletonFields:
             singletonProtectionRecord.fileField=fileSingletonField)
      }
    (*Defn*)irrelevantSingletonProtectionRecords==
      possiblyRelevantSingletonProtectionRecords \
      relevantSingletonProtectionRecords
    (*Defn*)uncoveredFileSingletonFields==
      {fileSingletonField \in fileSingletonFields:
        ( \A singletonProtectionRecord \in relevantSingletonProtectionRecords:
             singletonProtectionRecord.fileField#fileSingletonField)
      }
    (*Defn*)baseSingletonProtectionRecords==
      {ProtectionRecordProto(fileSingletonField,rw):
        fileSingletonField \in uncoveredFileSingletonFields
      }
    (*Defn*)newSingletonProtectionRecords==
      {
      [singletonProtectionRecord EXCEPT
        ![ie].beginSerNum=MinElement({@,ActionSerialNumber}),
        ![ie].expiration=MaxElement({@,expiration})
      ]
      :
        singletonProtectionRecord
        \in
        relevantSingletonProtectionRecords \union baseSingletonProtectionRecords
      }
    (*Defn*)updatedSingletonProtectionRecords==
      newSingletonProtectionRecords \union irrelevantSingletonProtectionRecords
    (*Defn*)updatedProtectionRecords==
      SingletonProtectionRecordSetToProtectionRecordSet(
        updatedSingletonProtectionRecords)
  IN
    (ActiveProtectionRecords')=
    (ActiveProtectionRecords \ relevantProtectionRecords)\union
    updatedProtectionRecords

(*Defn*)UpdateProtectionRecordsWithLeaseRelease(fileSingletonFields,rw)==
  (ActiveProtectionRecords')=
  UpdatedProtectionRecordsAfterLeaseRelease(
    ActiveProtectionRecords,fileSingletonFields,rw)

(*Defn*)
UpdateProtectionRecordsWithFileCreate(
  fileID,
  sharedValueLeaseTime,
  blackBoxReadSelfLeaseTime,
  blackBoxWriteSelfLeaseTime,
  blackBoxReadOtherLeaseTime,
  privateValueLeaseTime)==
  LET
    (*Defn*)sharedValueFileFields==
      UNION
      {MakeFileSharedValueFields(fileID),{MakeFileInfiniteChildField(fileID,{})}}
    (*Defn*)blackBoxSelfFileFields==
      UNION
      {
      {MakeFileOpenHandleField(fileID,BBSelf)},
      {MakeFileModeField(fileID,mode,BBSelf):mode \in Mode}
      }
    (*Defn*)blackBoxOtherFileFields==
      UNION
      {
      {MakeFileOpenHandleField(fileID,BBOther)},
      {MakeFileModeField(fileID,mode,BBOther):mode \in Mode}
      }
    (*Defn*)newProtectionRecords==
      UNION
      {
      {ProtectionRecordForCreate(fileField,PWrite,sharedValueLeaseTime):
        fileField \in sharedValueFileFields
      },
      {
      ProtectionRecordForCreate(
        MakeFileOpenHandleField(fileID,BBSelf),PRead,blackBoxReadSelfLeaseTime)
      },
      {ProtectionRecordForCreate(fileField,PWrite,blackBoxWriteSelfLeaseTime):
        fileField \in blackBoxSelfFileFields
      },
      {ProtectionRecordForCreate(fileField,PRead,blackBoxReadOtherLeaseTime):
        fileField \in blackBoxOtherFileFields
      },
      {
      ProtectionRecordForCreate(
        MakeFileBonaFideField(fileID),PRead,privateValueLeaseTime)
      }
      }
  IN
    (ActiveProtectionRecords')=
    ActiveProtectionRecords \union newProtectionRecords

(*Defn*)UpdateProtectionRecordsWithFileCloseAndUnlink(fileID)==
  LET
    (*Defn*)relevantFileSingletonFields==
      AllPeekableUnwarrantiedFileSingletonFields(fileID)\union
      AllPokeableUnwarrantiedFileSingletonFields(fileID)
    (*Defn*)relevantProtectionRecords==
      {protectionRecord \in ActiveProtectionRecords:
        ( \E fileSingletonField \in relevantFileSingletonFields,rw \in PReadOrWrite:
             ProtectionRecordIsRelevant(
               protectionRecord,fileSingletonField,rw,ActionSerialNumber,LateClock))
      }
    (*Defn*)updatedProtectionRecords==
      {[protectionRecord EXCEPT!.individual.endSerNum=ActionSerialNumber]:
        protectionRecord \in relevantProtectionRecords
      }
  IN
    (ActiveProtectionRecords')=
    (ActiveProtectionRecords \ relevantProtectionRecords)\union
    updatedProtectionRecords

(*Defn*)
UpdateProtectionRecordsWithOperationMessageDiscard(
  filesToEradicate,fileSingletonFieldsToRelease,serialNumbersToRestore)==
  LET
    (*Defn*)restoreRelevantProtectionRecords==
      {protectionRecord \in ActiveProtectionRecords:
        (protectionRecord.individual.endSerNum \in serialNumbersToRestore)
      }
    (*Defn*)restoreUpdatedProtectionRecords==
      {[protectionRecord EXCEPT!.individual.endSerNum=Infinity]:
        protectionRecord \in restoreRelevantProtectionRecords
      }
    (*Defn*)postRestoreActiveProtectionRecords==
      (ActiveProtectionRecords \ restoreRelevantProtectionRecords)\union
      restoreUpdatedProtectionRecords
    (*Defn*)postReleaseActiveProtectionRecords==
      UpdatedProtectionRecordsAfterLeaseRelease(
        postRestoreActiveProtectionRecords,fileSingletonFieldsToRelease,PWrite)
  IN
    (ActiveProtectionRecords')=
    ( {protectionRecord \in postReleaseActiveProtectionRecords:
        (protectionRecord.fileField.fileID \notin filesToEradicate)
      })

(* ********** Actions ****************************************************************************************************** *)

(*Defn*)DiscardDefunctProtectionRecord==
  \E protectionRecord \in ActiveProtectionRecords:
     /\ ( \A ie \in PIndividualOrEveryone:NowLaterThan(protectionRecord[ie].expiration))
     /\ (ActiveProtectionRecords')=ActiveProtectionRecords \ {protectionRecord}
====
