---- MODULE ServerFileOwnershipModule ----
(*`^\addcontentsline{toc}{section}{ServerFileOwnershipModule}^'*)

EXTENDS ServerLeasePredicatesModule,ServerMessageModule
VARIABLE OwnershipAuthorizingServer

VARIABLE IssuedDeeds

(*Defn*)OwnershipAuthorizingServerType==NilOr(Server)

(*Defn*)IssuedDeedsType==DeedSet

(*Defn*)OwnershipAuthorizingServerInit==Nil

(*Defn*)IssuedDeedsInit=={}

(* ********** Predicates *************************************************************************************************** *)

(*Defn*)IssuedFileOwnershipToServer(fileID,server)==
  \E deed \in IssuedDeeds:
     /\ FileGroupIncludesFile(deed.fileGroup,fileID)
     /\ deed.server=server

(*Defn*)FileHasBeenBorrowedByClient(fileID,client)==
  \E borrowerRecord \in ActiveBorrowerRecords:
     /\ fileID#FilesystemRoot
     /\ borrowerRecord.iparentFile=AllButLast(fileID)
     /\ borrowerRecord.minSuffix \leq Last(fileID)
     /\ borrowerRecord.maxSuffix \geq Last(fileID)
     /\ borrowerRecord.borrower=client

(*Defn*)FileHasBeenTransitivelyBorrowedByClient(fileID,client)==
  \E selfOrAncestorFileID \in FileID:
     /\ DoesSeqPrefixSeq(selfOrAncestorFileID,fileID)
     /\ FileHasBeenBorrowedByClient(selfOrAncestorFileID,client)

(* ********** Support Operators ******************************************************************************************** *)

(* When delegating fileID data, we need to ensure that expired leases don't get
	un-expired due to differences in clocks between the two servers.  The solution
	is to coerce all expiration times that are earlier than now to BeforeTimeBegins.
	That way, these times will certainly be earlier than now for whatever value
	of now the delegate server has. *)

(*Defn*)CoercedIssuedExpirationTime(expirationTime)==
  IF NowLaterThan(expirationTime)THEN BeforeTimeBegins ELSE expirationTime

(*Defn*)CoercedObtainedExpirationTime(expirationTime)==
  IF NowEarlierThan(expirationTime)THEN expirationTime ELSE BeforeTimeBegins

(* ********** Partial Actions ********************************************************************************************** *)

(*Defn*)NoChangeToFileOwnership==
  /\ UNCHANGED OwnershipAuthorizingServer
  /\ UNCHANGED IssuedDeeds
  /\ NoChangeToFileMap
  /\ UNCHANGED ActiveBorrowerRecords

(*Defn*)AcceptReturnedFile(fileID)==
  LET
    (*Defn*)prefix==AllButLast(fileID)(*Defn*)suffix==Last(fileID)
  IN
    \E borrowerRecord \in ActiveBorrowerRecords:
       /\ borrowerRecord.iparentFile=prefix
       /\ borrowerRecord.minSuffix \leq suffix
       /\ borrowerRecord.maxSuffix \geq suffix
       /\ IF borrowerRecord.minSuffix=suffix
          THEN
            IF borrowerRecord.maxSuffix=suffix
            THEN
              (ActiveBorrowerRecords')=ActiveBorrowerRecords \ {borrowerRecord}
            ELSE
              (ActiveBorrowerRecords')=
              (ActiveBorrowerRecords \ {borrowerRecord})\union
              {
              MakeBorrowerRecord(
                prefix,suffix+1,borrowerRecord.maxSuffix,borrowerRecord.borrower)
              }
          ELSE IF borrowerRecord.maxSuffix=suffix
          THEN
            (ActiveBorrowerRecords')=
            (ActiveBorrowerRecords \ {borrowerRecord})\union
            {
            MakeBorrowerRecord(
              prefix,borrowerRecord.minSuffix,suffix-1,borrowerRecord.borrower)
            }
          ELSE
            (ActiveBorrowerRecords')=
            (ActiveBorrowerRecords \ {borrowerRecord})\union
            {
            MakeBorrowerRecord(
              prefix,borrowerRecord.minSuffix,suffix-1,borrowerRecord.borrower),
            MakeBorrowerRecord(
              prefix,suffix+1,borrowerRecord.maxSuffix,borrowerRecord.borrower)
            }

(*Defn*)AcceptReturnedFileAndLendIchildren(fileID,newMaxSuffix)==
  LET
    (*Defn*)prefix==AllButLast(fileID)(*Defn*)suffix==Last(fileID)
  IN
    \E borrowerRecord \in ActiveBorrowerRecords:
       /\ borrowerRecord.iparentFile=prefix
       /\ borrowerRecord.minSuffix \leq suffix
       /\ borrowerRecord.maxSuffix \geq suffix
       /\ IF borrowerRecord.minSuffix=suffix
          THEN
            IF borrowerRecord.maxSuffix=suffix
            THEN
              (ActiveBorrowerRecords')=
              (ActiveBorrowerRecords \ {borrowerRecord})\union
              {MakeBorrowerRecord(fileID,1,newMaxSuffix,borrowerRecord.borrower)}
            ELSE
              (ActiveBorrowerRecords')=
              (ActiveBorrowerRecords \ {borrowerRecord})\union
              {
              MakeBorrowerRecord(
                prefix,suffix+1,borrowerRecord.maxSuffix,borrowerRecord.borrower),
              MakeBorrowerRecord(fileID,1,newMaxSuffix,borrowerRecord.borrower)
              }
          ELSE IF borrowerRecord.maxSuffix=suffix
          THEN
            (ActiveBorrowerRecords')=
            (ActiveBorrowerRecords \ {borrowerRecord})\union
            {
            MakeBorrowerRecord(
              prefix,borrowerRecord.minSuffix,suffix-1,borrowerRecord.borrower),
            MakeBorrowerRecord(fileID,1,newMaxSuffix,borrowerRecord.borrower)
            }
          ELSE
            (ActiveBorrowerRecords')=
            (ActiveBorrowerRecords \ {borrowerRecord})\union
            {
            MakeBorrowerRecord(
              prefix,borrowerRecord.minSuffix,suffix-1,borrowerRecord.borrower),
            MakeBorrowerRecord(
              prefix,suffix+1,borrowerRecord.maxSuffix,borrowerRecord.borrower),
            MakeBorrowerRecord(fileID,1,newMaxSuffix,borrowerRecord.borrower)
            }

(* ********** Actions ****************************************************************************************************** *)

(*Defn*)ProcessFileOwnershipNotificationMessage==
  \E sender \in Server,msg \in FileOwnershipNotificationMessage:
     /\ ReceiveMessage(sender,msg)
     /\ UNCHANGED FileValueTableState
     /\ UNCHANGED FileProtectionTableState
     /\ SendNoMessage
     /\ NoChangeToServerExistence
     /\ IF
          /\ FileGroup_isWellFormed(msg.deed.fileGroup)
          /\ ServerOwnsFileGroup(sender,msg.deed.fileGroup)
        THEN
          /\ UNCHANGED OwnershipAuthorizingServer
          /\ UNCHANGED IssuedDeeds
          /\ UNCHANGED ActiveBorrowerRecords
          /\ UpdateFileMapWithDeedFromServer(msg.deed,sender)
        ELSE
          NoChangeToFileOwnership

(*Defn*)ProcessFileOwnershipLoanRequestMessage==
  \E msg \in FileOwnershipLoanRequestMessage,requester \in Client:
     /\ ReceiveMessage(requester,msg)
     /\ UNCHANGED OwnershipAuthorizingServer
     /\ UNCHANGED IssuedDeeds
     /\ NoChangeToFileMap
     /\ NoChangeToServerExistence
     /\ IF ServerOwnsFile(thisHost,msg.iparentFile)
        THEN
          LET
            (*Defn*)minSuffix==FileProtectionTableState[msg.iparentFile].maxSuffix+1
          IN
            \E maxSuffix \in FileIDComponent:
               /\ maxSuffix \geq minSuffix
               /\ (ActiveBorrowerRecords')=
                  ActiveBorrowerRecords \union
                  MakeBorrowerRecord(msg.iparentFile,minSuffix,maxSuffix,requester)
               /\ UNCHANGED FileValueTableState
               /\ (FileProtectionTableState')=
                  [FileProtectionTableState EXCEPT![msg.iparentFile].maxSuffix=maxSuffix]
               /\ SendMessage(
                    requester,
                    MakeFileOwnershipLoanGrantMessage(msg.iparentFile,minSuffix,maxSuffix))
        ELSE
          /\ UNCHANGED ActiveBorrowerRecords
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ IF
               \A deed \in IssuedDeeds:
                  ( \neg FileGroupIncludesFile(deed.fileGroup,msg.iparentFile))
             THEN
               SendNoMessage
             ELSE
               \E deed \in IssuedDeeds:
                  /\ FileGroupIncludesFile(deed.fileGroup,msg.iparentFile)
                  /\ SendMessage(requester,MakeFileOwnershipNotificationMessage(deed))

(*Defn*)ProcessFileOwnershipQueryMessage==
  \E sender \in Server,msg \in FileOwnershipQueryMessage:
     /\ ReceiveMessage(sender,msg)
     /\ UNCHANGED FileValueTableState
     /\ UNCHANGED FileProtectionTableState
     /\ NoChangeToFileOwnership
     /\ NoChangeToServerExistence
     /\ IF
          \A deed \in IssuedDeeds:(\neg FileGroupIncludesFile(deed.fileGroup,msg.fileID))
        THEN
          SendNoMessage
        ELSE
          \E deed \in IssuedDeeds:
             /\ FileGroupIncludesFile(deed.fileGroup,msg.fileID)
             /\ SendMessage(sender,MakeFileOwnershipNotificationMessage(deed))

(*Defn*)InitiateDelegationOfFileOwnership==
  \E fileGroupSet \in FileGroupSet,delegate \in Server:
     LET
       (*Defn*)newDeeds==
         {MakeDeed(delegate,DummyMachine,fileGroup):fileGroup \in fileGroupSet}
       (*Defn*)delegatedFiles==
         {fileID \in FileID:
           (\E fileGroup \in fileGroupSet:FileGroupIncludesFile(fileGroup,fileID))
         }
       (*Defn*)fileValueData==
         [fileID \in delegatedFiles|->FileValueTableState[fileID]]
       (*Defn*)fileProtectionData==
         [fileID \in delegatedFiles|->
           [
             [
               [
                 [
                   [
                     [
                       [
                         [
                           [
                             [
                               [
                                 [
                                   [
                                     [
                                       [
                                         field2
                                         \in
                                         DOMAIN
                                         [field \in DOMAIN FileProtectionTableState[fileID]|->
                                           IF field \in FSharedValueFields
                                           THEN
                                             LET
                                               (*Defn*)AtSymbol002==(FileProtectionTableState[fileID])[field]
                                             IN
                                               [AtSymbol002 EXCEPT
                                                 !.individual=
                                                   [client \in DOMAIN@|->
                                                     IF client \in Client
                                                     THEN
                                                       LET
                                                         (*Defn*)AtSymbol003==@[client]
                                                       IN
                                                         [rw \in DOMAIN AtSymbol003|->
                                                           IF rw \in PReadOrWrite
                                                           THEN
                                                             LET
                                                               (*Defn*)AtSymbol004==AtSymbol003[rw]
                                                             IN
                                                               CoercedIssuedExpirationTime(AtSymbol004)
                                                           ELSE
                                                             AtSymbol003[rw]
                                                         ]
                                                     ELSE
                                                       @[client]
                                                   ]
                                               ]
                                           ELSE
                                             (FileProtectionTableState[fileID])[field]
                                         ]
                                       |->
                                         IF field2 \in FSharedValueFields
                                         THEN
                                           LET
                                             (*Defn*)AtSymbol001==
                                               [field \in DOMAIN FileProtectionTableState[fileID]|->
                                                 IF field \in FSharedValueFields
                                                 THEN
                                                   LET
                                                     (*Defn*)AtSymbol005==(FileProtectionTableState[fileID])[field]
                                                   IN
                                                     [AtSymbol005 EXCEPT
                                                       !.individual=
                                                         [client \in DOMAIN@|->
                                                           IF client \in Client
                                                           THEN
                                                             LET
                                                               (*Defn*)AtSymbol006==@[client]
                                                             IN
                                                               [rw \in DOMAIN AtSymbol006|->
                                                                 IF rw \in PReadOrWrite
                                                                 THEN
                                                                   LET
                                                                     (*Defn*)AtSymbol007==AtSymbol006[rw]
                                                                   IN
                                                                     CoercedIssuedExpirationTime(AtSymbol007)
                                                                 ELSE
                                                                   AtSymbol006[rw]
                                                               ]
                                                           ELSE
                                                             @[client]
                                                         ]
                                                     ]
                                                 ELSE
                                                   (FileProtectionTableState[fileID])[field]
                                               ]
                                               [
                                               field2
                                               ]
                                           IN
                                             [AtSymbol001 EXCEPT!.everyone.read=CoercedIssuedExpirationTime(@)]
                                         ELSE
                                           [field \in DOMAIN FileProtectionTableState[fileID]|->
                                             IF field \in FSharedValueFields
                                             THEN
                                               LET
                                                 (*Defn*)AtSymbol008==(FileProtectionTableState[fileID])[field]
                                               IN
                                                 [AtSymbol008 EXCEPT
                                                   !.individual=
                                                     [client \in DOMAIN@|->
                                                       IF client \in Client
                                                       THEN
                                                         LET
                                                           (*Defn*)AtSymbol009==@[client]
                                                         IN
                                                           [rw \in DOMAIN AtSymbol009|->
                                                             IF rw \in PReadOrWrite
                                                             THEN
                                                               LET
                                                                 (*Defn*)AtSymbol010==AtSymbol009[rw]
                                                               IN
                                                                 CoercedIssuedExpirationTime(AtSymbol010)
                                                             ELSE
                                                               AtSymbol009[rw]
                                                           ]
                                                       ELSE
                                                         @[client]
                                                     ]
                                                 ]
                                             ELSE
                                               (FileProtectionTableState[fileID])[field]
                                           ]
                                           [
                                           field2
                                           ]
                                       ]
                                     EXCEPT
                                       !.children=
                                         [@EXCEPT
                                           !.singleton=
                                             [label \in DOMAIN@|->
                                               IF label \in Label
                                               THEN
                                                 LET
                                                   (*Defn*)AtSymbol011==@[label]
                                                 IN
                                                   [AtSymbol011 EXCEPT
                                                     !.individual=
                                                       [client \in DOMAIN@|->
                                                         IF client \in Client
                                                         THEN
                                                           LET
                                                             (*Defn*)AtSymbol012==@[client]
                                                           IN
                                                             [rw \in DOMAIN AtSymbol012|->
                                                               IF rw \in PReadOrWrite
                                                               THEN
                                                                 LET
                                                                   (*Defn*)AtSymbol013==AtSymbol012[rw]
                                                                 IN
                                                                   CoercedIssuedExpirationTime(AtSymbol013)
                                                               ELSE
                                                                 AtSymbol012[rw]
                                                             ]
                                                         ELSE
                                                           @[client]
                                                       ]
                                                   ]
                                               ELSE
                                                 @[label]
                                             ]
                                         ]
                                     ]
                                   EXCEPT
                                     !.children=
                                       [@EXCEPT
                                         !.singleton=
                                           [label \in DOMAIN@|->
                                             IF label \in Label
                                             THEN
                                               LET
                                                 (*Defn*)AtSymbol014==@[label]
                                               IN
                                                 [AtSymbol014 EXCEPT!.everyone.read=CoercedIssuedExpirationTime(@)]
                                             ELSE
                                               @[label]
                                           ]
                                       ]
                                   ]
                                 EXCEPT
                                   !.children.infinite.write=CoercedIssuedExpirationTime(@)
                                 ]
                               EXCEPT
                                 !.openHandle=
                                   [@EXCEPT
                                     !.self=
                                       [@EXCEPT
                                         !.individual=
                                           [client \in DOMAIN@|->
                                             IF client \in Client
                                             THEN
                                               LET
                                                 (*Defn*)AtSymbol015==@[client]
                                               IN
                                                 [rw \in DOMAIN AtSymbol015|->
                                                   IF rw \in PReadOrWrite
                                                   THEN
                                                     LET
                                                       (*Defn*)AtSymbol016==AtSymbol015[rw]
                                                     IN
                                                       CoercedIssuedExpirationTime(AtSymbol016)
                                                   ELSE
                                                     AtSymbol015[rw]
                                                 ]
                                             ELSE
                                               @[client]
                                           ]
                                       ]
                                   ]
                               ]
                             EXCEPT
                               !.openHandle=
                                 [@EXCEPT
                                   !.self=
                                     [@EXCEPT
                                       !.everyone=
                                         [rw \in DOMAIN@|->
                                           IF rw \in PReadOrWrite
                                           THEN
                                             LET(*Defn*)AtSymbol017==@[rw]IN CoercedIssuedExpirationTime(AtSymbol017)
                                           ELSE
                                             @[rw]
                                         ]
                                     ]
                                 ]
                             ]
                           EXCEPT
                             !.openHandle=
                               [@EXCEPT
                                 !.other=
                                   [@EXCEPT
                                     !.individual=
                                       [client \in DOMAIN@|->
                                         IF client \in Client
                                         THEN
                                           LET
                                             (*Defn*)AtSymbol018==@[client]
                                           IN
                                             [AtSymbol018 EXCEPT!.read=CoercedIssuedExpirationTime(@)]
                                         ELSE
                                           @[client]
                                       ]
                                   ]
                               ]
                           ]
                         EXCEPT
                           !.openHandle.other.everyone.read=CoercedIssuedExpirationTime(@)
                         ]
                       EXCEPT
                         !.modes=
                           [mode \in DOMAIN@|->
                             IF mode \in Mode
                             THEN
                               LET
                                 (*Defn*)AtSymbol019==@[mode]
                               IN
                                 [AtSymbol019 EXCEPT
                                   !.self=
                                     [@EXCEPT
                                       !.individual=
                                         [client \in DOMAIN@|->
                                           IF client \in Client
                                           THEN
                                             LET
                                               (*Defn*)AtSymbol020==@[client]
                                             IN
                                               [rw \in DOMAIN AtSymbol020|->
                                                 IF rw \in PReadOrWrite
                                                 THEN
                                                   LET
                                                     (*Defn*)AtSymbol021==AtSymbol020[rw]
                                                   IN
                                                     CoercedIssuedExpirationTime(AtSymbol021)
                                                 ELSE
                                                   AtSymbol020[rw]
                                               ]
                                           ELSE
                                             @[client]
                                         ]
                                     ]
                                 ]
                             ELSE
                               @[mode]
                           ]
                       ]
                     EXCEPT
                       !.modes=
                         [mode \in DOMAIN@|->
                           IF mode \in Mode
                           THEN
                             LET
                               (*Defn*)AtSymbol022==@[mode]
                             IN
                               [AtSymbol022 EXCEPT
                                 !.self=
                                   [@EXCEPT
                                     !.everyone=
                                       [rw \in DOMAIN@|->
                                         IF rw \in PReadOrWrite
                                         THEN
                                           LET(*Defn*)AtSymbol023==@[rw]IN CoercedIssuedExpirationTime(AtSymbol023)
                                         ELSE
                                           @[rw]
                                       ]
                                   ]
                               ]
                           ELSE
                             @[mode]
                         ]
                     ]
                   EXCEPT
                     !.modes=
                       [mode \in DOMAIN@|->
                         IF mode \in Mode
                         THEN
                           LET
                             (*Defn*)AtSymbol024==@[mode]
                           IN
                             [AtSymbol024 EXCEPT!.other.individual.read=CoercedIssuedExpirationTime(@)]
                         ELSE
                           @[mode]
                       ]
                   ]
                 EXCEPT
                   !.modes=
                     [mode \in DOMAIN@|->
                       IF mode \in Mode
                       THEN
                         LET
                           (*Defn*)AtSymbol025==@[mode]
                         IN
                           [AtSymbol025 EXCEPT!.other.everyone.read=CoercedIssuedExpirationTime(@)]
                       ELSE
                         @[mode]
                     ]
                 ]
               EXCEPT
                 !.path.up=CoercedObtainedExpirationTime(@)
               ]
             EXCEPT
               !.path=
                 [@EXCEPT
                   !.down=
                     [label \in DOMAIN@|->
                       IF label \in Label
                       THEN
                         LET(*Defn*)AtSymbol026==@[label]IN CoercedIssuedExpirationTime(AtSymbol026)
                       ELSE
                         @[label]
                     ]
                 ]
             ]
           EXCEPT
             !.path=
               [@EXCEPT
                 !.individual=
                   [client \in DOMAIN@|->
                     IF client \in Client
                     THEN
                       LET
                         (*Defn*)AtSymbol027==@[client]
                       IN
                         [AtSymbol027 EXCEPT!.read=CoercedIssuedExpirationTime(@)]
                     ELSE
                       @[client]
                   ]
               ]
           ]
         ]
       (*Defn*)fileMappingsFromRoots==
         {MakeFileMapping(fileGroup.rootPrefix,delegate):fileGroup \in fileGroupSet}
       (*Defn*)supersededOldFileMappings==
         {MakeFileMapping(fileGroup.rootPrefix,thisHost):fileGroup \in fileGroupSet}
       (*Defn*)newFileMap==
         (FileMap \ supersededOldFileMappings)\union fileMappingsFromRoots
       (*Defn*)concernedClients==
         {client \in Client:
           ( \E fileID \in delegatedFiles:
                \/ ( \E svf \in FSharedValueFields,rw \in PReadOrWrite:
                        ClientHasIndividualSVLease(
                          client,(FileProtectionTableState[fileID])[svf],rw))
                \/ ( \E label \in Label,rw \in PReadOrWrite:
                        ClientHasIndividualChildLease(client,fileID,label,rw))
                \/ ( \E so \in BBSelfOrOther,rw \in PReadOrWrite:
                        /\ (\neg(so=BBOther/\ rw=PWrite))
                        /\ ClientHasIndividualBBLease(
                             client,FileProtectionTableState[fileID].openHandle,so,rw))
                \/ ( \E mode \in Mode,so \in BBSelfOrOther,rw \in PReadOrWrite:
                        /\ (\neg(so=BBOther/\ rw=PWrite))
                        /\ ClientHasIndividualBBLease(
                             client,FileProtectionTableState[fileID].modes[mode],so,rw)))
         }
       (*Defn*)addressedClientMessages==
         {MakeAddressedMessage(client,MakeFileOwnershipNotificationMessage(deed)):
           client \in concernedClients,deed \in newDeeds
         }
     IN
       /\ ( \A fileGroup \in fileGroupSet:
               /\ FileGroup_isWellFormed(fileGroup)
               /\ ServerOwnsFileGroup(thisHost,fileGroup)
               /\ FileHasBeenConceived(fileGroup.rootPrefix)
               /\ (\neg FileHasBeenBorrowed(fileGroup.rootPrefix))
               /\ ( \A cutPrefix \in fileGroup.cutPrefixSet:
                       ( \neg ServerOwnsFile(thisHost,cutPrefix)))
               /\ ( \A otherFileGroup \in fileGroupSet:
                       otherFileGroup#fileGroup=>
                       ( \A fileID \in FileID:
                            FileGroupIncludesFile(otherFileGroup,fileID)=>
                            ( \neg FileGroupIncludesFile(fileGroup,fileID)))))
       /\ ReceiveNoMessage
       /\ InitiateCreationOfDelegateServer(delegate)
       /\ UNCHANGED OwnershipAuthorizingServer
       /\ (IssuedDeeds')=IssuedDeeds \union newDeeds
       /\ (FileMap')=newFileMap
       /\ (FileValueTableState')=
          [fileID \in DOMAIN FileValueTableState|->
            IF fileID \in delegatedFiles
            THEN
              LET(*Defn*)AtSymbol028==FileValueTableState[fileID]IN FileValueInit
            ELSE
              FileValueTableState[fileID]
          ]
       /\ (FileProtectionTableState')=
          [fileID \in DOMAIN FileProtectionTableState|->
            IF fileID \in delegatedFiles
            THEN
              LET(*Defn*)AtSymbol029==FileProtectionTableState[fileID]IN FileProtectionInit
            ELSE
              FileProtectionTableState[fileID]
          ]
       /\ ( \E delegatedBorrowerRecords \in BorrowerRecordSet,
               retainedBorrowerRecords \in BorrowerRecordSet
               :
               /\ delegatedBorrowerRecords \union retainedBorrowerRecords=ActiveBorrowerRecords
               /\ delegatedBorrowerRecords \intersect retainedBorrowerRecords={}
               /\ ( \A delegatedBorrowerRecord \in delegatedBorrowerRecords:
                       ( \E fileGroup \in fileGroupSet:
                            FileGroupIncludesFile(fileGroup,delegatedBorrowerRecord.iparentFile)))
               /\ ( \A retainedBorrowerRecord \in retainedBorrowerRecords,fileGroup \in fileGroupSet
                       :
                       ( \neg FileGroupIncludesFile(fileGroup,retainedBorrowerRecord.iparentFile)))
               /\ (ActiveBorrowerRecords')=retainedBorrowerRecords
               /\ SendAddressedMessageSet(
                    addressedClientMessages \union
                    {
                    MakeAddressedMessage(
                      delegate,
                      MakeFileOwnershipDelegationMessage(
                        newFileMap,fileValueData,fileProtectionData,delegatedBorrowerRecords))
                    }))

(*Defn*)CompleteDelegationOfFileOwnership==
  \E creator \in Server,msg \in FileOwnershipDelegationMessage:
     /\ ReceiveMessage(creator,msg)
     /\ CompleteCreationOfThisServer(creator)
     /\ (OwnershipAuthorizingServer')=creator
     /\ (IssuedDeeds')={}
     /\ (FileMap')=msg.fileMap
     /\ SendNoMessage
     /\ (FileValueTableState')=
        [fileID \in FileID|->
          IF fileID \in DOMAIN msg.fileValueData
          THEN
            msg.fileValueData[fileID]
          ELSE
            FileValueTableState[fileID]
        ]
     /\ (FileProtectionTableState')=
        [fileID \in FileID|->
          IF fileID \in DOMAIN msg.fileProtectionData
          THEN
            msg.fileProtectionData[fileID]
          ELSE
            FileProtectionTableState[fileID]
        ]
     /\ (ActiveBorrowerRecords')=msg.borrowerRecordSet
====
