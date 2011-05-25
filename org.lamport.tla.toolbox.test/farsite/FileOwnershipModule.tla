---- MODULE FileOwnershipModule ----
(*`^\addcontentsline{toc}{section}{FileOwnershipModule}^'*)

EXTENDS FileFieldModule
(* ********** Definitions ************************************************************************************************* *)

(*Defn*)FileMapping==[prefix:FileID,server:Server]
(*Defn*)MakeFileMapping(i_prefix,i_server)==
  [prefix|->i_prefix,server|->i_server]

(*Defn*)FileMappingSet==SUBSET FileMapping

(*Defn*)FileGroup==[rootPrefix:FileID,cutPrefixSet:FileSet]
(*Defn*)FileGroup_isWellFormed(this)==
  \A cutPrefix \in this.cutPrefixSet:
     /\ DoesSeqProperlyPrefixSeq(this.rootPrefix,cutPrefix)
     /\ ( \A otherCutPrefix \in this.cutPrefixSet:
             otherCutPrefix#cutPrefix=>(\neg DoesSeqPrefixSeq(otherCutPrefix,cutPrefix)))
(*Defn*)MakeFileGroup(i_rootPrefix,i_cutPrefixSet)==
  [rootPrefix|->i_rootPrefix,cutPrefixSet|->i_cutPrefixSet]

(*Defn*)FileGroupSet==SUBSET FileGroup

(*Defn*)Deed==[server:Server,machine:Machine,fileGroup:FileGroup]
(*Defn*)MakeDeed(i_server,i_machine,i_fileGroup)==
  [server|->i_server,machine|->i_machine,fileGroup|->i_fileGroup]

(*Defn*)DeedSet==SUBSET Deed

(*Defn*)BorrowerRecord==
  [
    iparentFile:FileID,
    minSuffix:FileIDComponent,
    maxSuffix:FileIDComponent,
    borrower:Client
  ]
(*Defn*)
MakeBorrowerRecord(i_iparentFile,i_minSuffix,i_maxSuffix,i_borrower)==
  [
  iparentFile|->i_iparentFile,
  minSuffix|->i_minSuffix,
  maxSuffix|->i_maxSuffix,
  borrower|->i_borrower
  ]

(*Defn*)BorrowerRecordIntegrityConstraint(BorrowerRecordRelvar)==
  \A tuple1 \in BorrowerRecordRelvar,tuple2 \in BorrowerRecordRelvar:
     tuple1#tuple2/\ tuple1.iparentFile=tuple2.iparentFile=>
     \/ tuple1.maxSuffix<tuple2.minSuffix
     \/ tuple2.maxSuffix<tuple1.minSuffix

(*Defn*)BorrowerRecordIntegrityConstraint2(BorrowerRecordRelvar)==
  \A tuple \in BorrowerRecordRelvar:tuple.minSuffix \leq tuple.maxSuffix

(*Defn*)BorrowerRecordSet==SUBSET BorrowerRecord

VARIABLE FileMap

(*Defn*)FileMapType==FileMappingSet

(*Defn*)FileMapInit=={MakeFileMapping(FilesystemRoot,RootServer)}

VARIABLE ActiveBorrowerRecords

(*Defn*)ActiveBorrowerRecordsType==BorrowerRecordSet

(*Defn*)ActiveBorrowerRecordsInit=={}

(* ********** Predicates ************************************************************************************************** *)

(*Defn*)FileHasLongestMatchingPrefixMapping(fileID,fileMapping)==
  /\ fileMapping \in FileMap
  /\ DoesSeqPrefixSeq(fileMapping.prefix,fileID)
  /\ ( \A otherFileMapping \in FileMap:
          DoesSeqPrefixSeq(otherFileMapping.prefix,fileID)=>
          DoesSeqPrefixSeq(otherFileMapping.prefix,fileMapping.prefix))

(*Defn*)FileGroupIncludesFile(fileGroup,fileID)==
  /\ DoesSeqPrefixSeq(fileGroup.rootPrefix,fileID)
  /\ ( \A cutFile \in fileGroup.cutPrefixSet:(\neg DoesSeqPrefixSeq(cutFile,fileID)))

(*Defn*)ServerOwnsFileGroup(server,fileGroup)==
  \E fileMapping \in FileMap:
     /\ fileMapping.server=server
     /\ FileHasLongestMatchingPrefixMapping(fileGroup.rootPrefix,fileMapping)
     /\ ( \A otherFileMapping \in FileMap:
             DoesSeqProperlyPrefixSeq(fileGroup.rootPrefix,otherFileMapping.prefix)=>
             ( \E cutPrefix \in fileGroup.cutPrefixSet:
                  DoesSeqPrefixSeq(cutPrefix,otherFileMapping.prefix)))

(*Defn*)ServerOwnsFile(server,fileID)==
  \E fileMapping \in FileMap:
     /\ fileMapping.server=server
     /\ FileHasLongestMatchingPrefixMapping(fileID,fileMapping)

(*Defn*)ServerOverseesFile(server,fileID)==
  \E fileMapping \in FileMap:
     /\ fileMapping.server=server
     /\ DoesSeqPrefixSeq(fileMapping.prefix,fileID)

(*Defn*)BorrowerRecordIsWellFormed(borrowerRecord)==
  borrowerRecord.minSuffix \leq borrowerRecord.maxSuffix

(*Defn*)BorrowerRecordSetIsWellFormed(borrowerRecordSet)==
  /\ ( \A borrowerRecord \in borrowerRecordSet:
          BorrowerRecordIsWellFormed(borrowerRecord))
  /\ ( \A borrowerRecord1 \in borrowerRecordSet,borrowerRecord2 \in borrowerRecordSet:
          borrowerRecord1#borrowerRecord2=>
          \/ borrowerRecord1.maxSuffix \leq borrowerRecord1.minSuffix
          \/ borrowerRecord1.minSuffix \geq borrowerRecord1.maxSuffix)

(*Defn*)BorrowerRecordIncludesFile(borrowerRecord,fileID)==
  /\ fileID#FilesystemRoot
  /\ borrowerRecord.iparentFile=AllButLast(fileID)
  /\ borrowerRecord.minSuffix \leq Last(fileID)
  /\ borrowerRecord.maxSuffix \geq Last(fileID)

(*Defn*)BorrowerRecordSetIncludesFile(borrowerRecordSet,fileID)==
  \E borrowerRecord \in borrowerRecordSet:
     BorrowerRecordIncludesFile(borrowerRecord,fileID)

(*Defn*)FileHasBeenBorrowed(fileID)==
  BorrowerRecordSetIncludesFile(ActiveBorrowerRecords,fileID)

(* ********** Partial Actions ********************************************************************************************* *)

(*Defn*)UpdateFileMapWithDeedFromServer(deed,sender)==
  LET
    (*Defn*)fileMappingsFromDeedRoot==
      {MakeFileMapping(deed.fileGroup.rootPrefix,deed.server)}
    (*Defn*)fileMappingsFromDeedCuts==
      {MakeFileMapping(cutPrefix,sender):cutPrefix \in deed.fileGroup.cutPrefixSet}
    (*Defn*)deedFileMappings==
      fileMappingsFromDeedRoot \union fileMappingsFromDeedCuts
    (*Defn*)supersededOldFileMappings==
      {MakeFileMapping(deed.fileGroup.rootPrefix,sender)}
    (*Defn*)supersededDeedFileMappings==
      {deedFileMapping \in fileMappingsFromDeedCuts:
        (\E oldFileMapping \in FileMap:oldFileMapping.prefix=deedFileMapping.prefix)
      }
  IN
    (FileMap')=
    (FileMap \ supersededOldFileMappings)\union
    ( deedFileMappings \ supersededDeedFileMappings)

(*Defn*)NoChangeToFileMap==UNCHANGED FileMap
====
