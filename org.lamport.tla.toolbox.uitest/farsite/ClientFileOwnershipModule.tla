---- MODULE ClientFileOwnershipModule ----
(*`^\addcontentsline{toc}{section}{ClientFileOwnershipModule}^'*)

EXTENDS ClientLogModule
(* ********** Predicates ************************************************************************************************** *)

(*Defn*)IchildOfFileHasBeenBorrowed(iparentFile)==
  \E borrowerRecord \in ActiveBorrowerRecords:
     borrowerRecord.iparentFile=iparentFile

(* ********** Partial Actions ********************************************************************************************* *)

(*Defn*)NoChangeToFileOwnership==
  /\ NoChangeToFileMap
  /\ UNCHANGED ActiveBorrowerRecords

(*Defn*)RetrieveBorrowedFile(iparentFile,borrowedFile)==
  \E borrowerRecord \in ActiveBorrowerRecords:
     /\ borrowerRecord.iparentFile=iparentFile
     /\ borrowedFile=Append(iparentFile,borrowerRecord.minSuffix)
     /\ IF borrowerRecord.minSuffix=borrowerRecord.maxSuffix
        THEN
          (ActiveBorrowerRecords')=ActiveBorrowerRecords \ {borrowerRecord}
        ELSE
          (ActiveBorrowerRecords')=
          (ActiveBorrowerRecords \ {borrowerRecord})\union
          {
          MakeBorrowerRecord(
            borrowerRecord.iparentFile,
            borrowerRecord.minSuffix+1,
            borrowerRecord.maxSuffix,
            thisHost)
          }

(*Defn*)
RetrieveBorrowedFileAndBorrowIchildren(
  iparentFile,borrowedFile,newMaxSuffix)==
  \E borrowerRecord \in ActiveBorrowerRecords:
     /\ borrowerRecord.iparentFile=iparentFile
     /\ borrowedFile=Append(iparentFile,borrowerRecord.minSuffix)
     /\ IF borrowerRecord.minSuffix=borrowerRecord.maxSuffix
        THEN
          (ActiveBorrowerRecords')=
          (ActiveBorrowerRecords \ {borrowerRecord})\union
          {MakeBorrowerRecord(borrowedFile,1,newMaxSuffix,thisHost)}
        ELSE
          (ActiveBorrowerRecords')=
          (ActiveBorrowerRecords \ {borrowerRecord})\union
          {
          MakeBorrowerRecord(
            borrowerRecord.iparentFile,
            borrowerRecord.minSuffix+1,
            borrowerRecord.maxSuffix,
            thisHost),
          MakeBorrowerRecord(borrowedFile,1,newMaxSuffix,thisHost)
          }

(*Defn*)LocallyBorrowIchild(iparentFile)==
  \E newMaxSuffix \in FileIDComponent,borrowerRecord \in ActiveBorrowerRecords:
     /\ borrowerRecord.iparentFile=iparentFile
     /\ newMaxSuffix>borrowerRecord.maxSuffix
     /\ UpdateCreateFileMessageInLogWithNewBorrowedMaxSuffix(
          iparentFile,newMaxSuffix)
     /\ (ActiveBorrowerRecords')=
        (ActiveBorrowerRecords \ {borrowerRecord})\union
        {MakeBorrowerRecord(iparentFile,1,newMaxSuffix,thisHost)}

(* ********** Actions ***************************************************************************************************** *)

(*Defn*)ProcessFileOwnershipNotificationMessage==
  \E sender \in Server,msg \in FileOwnershipNotificationMessage:
     /\ ReceiveMessage(sender,msg)
     /\ UNCHANGED ActiveBorrowerRecords
     /\ IF
          /\ FileGroup_isWellFormed(msg.deed.fileGroup)
          /\ ServerOwnsFileGroup(sender,msg.deed.fileGroup)
        THEN
          UpdateFileMapWithDeedFromServer(msg.deed,sender)
        ELSE
          NoChangeToFileMap

(*Defn*)ProcessFileOwnershipLoanGrantMessage==
  \E server \in Server,msg \in FileOwnershipLoanGrantMessage:
     /\ ReceiveMessage(server,msg)
     /\ NoChangeToFileMap
     /\ IF \neg ServerOwnsFile(server,msg.iparentFile)
        THEN
          UNCHANGED ActiveBorrowerRecords
        ELSE IF msg.minSuffix>msg.maxSuffix
        THEN
          UNCHANGED ActiveBorrowerRecords
        ELSE IF
          \E borrowerRecord \in ActiveBorrowerRecords:
             /\ borrowerRecord.iparentFile=msg.iparentFile
             /\ borrowerRecord.maxSuffix \geq msg.minSuffix
        THEN
          UNCHANGED ActiveBorrowerRecords
        ELSE
          (ActiveBorrowerRecords')=
          ActiveBorrowerRecords \union
          MakeBorrowerRecord(msg.iparentFile,msg.minSuffix,msg.maxSuffix,thisHost)
====
