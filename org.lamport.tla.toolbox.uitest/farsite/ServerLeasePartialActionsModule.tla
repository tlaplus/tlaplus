---- MODULE ServerLeasePartialActionsModule ----
(*`^\addcontentsline{toc}{section}{ServerLeasePartialActionsModule}^'*)

EXTENDS ServerFileOwnershipModule
(* ********** Shared-value lease grant partial actions ********************************************************************* *)

(* 
	The only enabling condition for these partial actions is that no client holds a
	reservation on the lease.  All other preconditions must be established by the
	actions that make use of these partial actions.
 *)

(*Defn*)GrantSVLease(client,fileID,field,rw)==
  \E leaseTime \in ServerShortLeaseTimeRange:
     /\ (\neg SharedValueLeaseReserved((FileProtectionTableState[fileID])[field]))
     /\ UNCHANGED FileValueTableState
     /\ (FileProtectionTableState')=
        [FileProtectionTableState EXCEPT
          ![fileID][field].individual[client][rw]=(LateClock+leaseTime)
        ]
     /\ SendMessage(
          client,
          MakeSingletonLeaseGrantMessage(
            MakeFileSharedValueField(fileID,field),
            rw,
            (FileValueTableState[fileID])[field],
            FALSE,
            LateClock+leaseTime))

(*Defn*)GrantOrExtendSVLease(client,fileID,field,rw)==
  LET
    (*Defn*)extension==
      ClientHasIndividualSVLease(
        client,(FileProtectionTableState[fileID])[field],rw)
  IN
    \E leaseTime \in ServerShortLeaseTimeRange:
       /\ (\neg SharedValueLeaseReserved((FileProtectionTableState[fileID])[field]))
       /\ ( extension=>
            LateClock+leaseTime>
            ((FileProtectionTableState[fileID])[field].individual[client])[rw])
       /\ UNCHANGED FileValueTableState
       /\ (FileProtectionTableState')=
          [FileProtectionTableState EXCEPT
            ![fileID][field].individual[client][rw]=(LateClock+leaseTime)
          ]
       /\ SendMessage(
            client,
            MakeSingletonLeaseGrantMessage(
              MakeFileSharedValueField(fileID,field),
              rw,
              IF extension THEN Nil ELSE(FileValueTableState[fileID])[field],
              extension,
              LateClock+leaseTime))

(*Defn*)GrantSingletonChildLease(client,fileID,label,rw)==
  \E leaseTime \in ServerShortLeaseTimeRange:
     /\ ( \neg
          SharedValueLeaseReserved(
            FileProtectionTableState[fileID].children.singleton[label]))
     /\ UNCHANGED FileValueTableState
     /\ (FileProtectionTableState')=
        [FileProtectionTableState EXCEPT
          ![fileID].children.singleton[label].individual[client][rw]=
            (LateClock+leaseTime)
        ]
     /\ SendMessage(
          client,
          MakeSingletonLeaseGrantMessage(
            MakeFileChildField(fileID,label),
            rw,
            FileValueTableState[fileID].children[label],
            FALSE,
            LateClock+leaseTime))

(*Defn*)GrantOrExtendSingletonChildLease(client,fileID,label,rw)==
  LET
    (*Defn*)extension==ClientHasIndividualChildLease(client,fileID,label,rw)
  IN
    \E leaseTime \in ServerShortLeaseTimeRange:
       /\ ( \neg
            SharedValueLeaseReserved(
              FileProtectionTableState[fileID].children.singleton[label]))
       /\ ( extension=>
            LateClock+leaseTime>
            ( FileProtectionTableState[fileID].children.singleton[label].individual
              [
              client
              ])
            [
            rw
            ])
       /\ UNCHANGED FileValueTableState
       /\ (FileProtectionTableState')=
          [FileProtectionTableState EXCEPT
            ![fileID].children.singleton[label].individual[client][rw]=
              (LateClock+leaseTime)
          ]
       /\ SendMessage(
            client,
            MakeSingletonLeaseGrantMessage(
              MakeFileChildField(fileID,label),
              rw,
              IF extension THEN Nil ELSE FileValueTableState[fileID].children[label],
              extension,
              LateClock+leaseTime))

(*Defn*)GrantInfiniteChildLease(client,fileID)==
  LET
    (*Defn*)excludedLabels==
      {label \in Label:
        ( \/ ( \E someClient \in Client:
                  ClientHasReadOrWriteChildLease(someClient,fileID,label))
          \/ SharedValueLeaseReserved(
               FileProtectionTableState[fileID].children.singleton[label])
          \/ DownPathLeaseIssued(fileID,label))
      }
    (*Defn*)nonNilLabels==
      {label \in Label:
        ( /\ label \notin excludedLabels
          /\ FileValueTableState[fileID].children[label]#Nil)
      }
    (*Defn*)childValueSet==
      {MakeChildValue(label,FileValueTableState[fileID].children[label]):
        label \in nonNilLabels
      }
  IN
    \E leaseTime \in ServerShortLeaseTimeRange:
       /\ UNCHANGED FileValueTableState
       /\ (FileProtectionTableState')=
          [FileProtectionTableState EXCEPT
            ![fileID].children.infinite=
              InfiniteChild(excludedLabels,client,LateClock+leaseTime)
          ]
       /\ SendMessage(
            client,
            MakeInfiniteChildLeaseGrantMessage(
              MakeFileInfiniteChildField(fileID,excludedLabels),
              childValueSet,
              FALSE,
              LateClock+leaseTime))

(*Defn*)ExtendInfiniteChildLease(client,fileID)==
  LET
    (*Defn*)excludedLabels==
      FileProtectionTableState[fileID].children.infinite.excludedLabels
  IN
    \E leaseTime \in ServerShortLeaseTimeRange:
       /\ LateClock+leaseTime>FileProtectionTableState[fileID].children.infinite.write
       /\ UNCHANGED FileValueTableState
       /\ (FileProtectionTableState')=
          [FileProtectionTableState EXCEPT
            ![fileID].children.infinite.write=(LateClock+leaseTime)
          ]
       /\ SendMessage(
            client,
            MakeInfiniteChildLeaseGrantMessage(
              MakeFileInfiniteChildField(fileID,excludedLabels),
              {},
              TRUE,
              LateClock+leaseTime))

(* ********** OpenHandle lease grant partial actions *********************************************************************** *)

(* 
	There are no enabling conditions for these partial actions.  All preconditions
	must be established by the actions that make use of these partial actions.
 *)

(*Defn*)GrantOpenHandleReadSelfLease(client,fileID)==
  \E leaseTime \in ServerLongLeaseTimeRange:
     /\ UNCHANGED FileValueTableState
     /\ (FileProtectionTableState')=
        [FileProtectionTableState EXCEPT
          ![fileID].openHandle.self.individual[client].read=(LateClock+leaseTime)
        ]
     /\ SendMessage(
          client,
          MakeSingletonLeaseGrantMessage(
            MakeFileOpenHandleField(fileID,BBSelf),
            PRead,
            FileValueTableState[fileID].openHandle.self[client],
            FALSE,
            LateClock+leaseTime))

(*Defn*)GrantOpenHandleWriteSelfLease(client,fileID)==
  \E leaseTime \in ServerShortLeaseTimeRange:
     /\ UNCHANGED FileValueTableState
     /\ (FileProtectionTableState')=
        [FileProtectionTableState EXCEPT
          ![fileID].openHandle.self.individual[client].write=(LateClock+leaseTime)
        ]
     /\ SendMessage(
          client,
          MakeSingletonLeaseGrantMessage(
            MakeFileOpenHandleField(fileID,BBSelf),PWrite,Nil,FALSE,LateClock+leaseTime))

(*Defn*)GrantOpenHandleReadOtherLease(client,fileID,value)==
  \E leaseTime \in ServerShortLeaseTimeRange:
     /\ (FileValueTableState')=
        [FileValueTableState EXCEPT![fileID].openHandle.other[client]=value]
     /\ (FileProtectionTableState')=
        [FileProtectionTableState EXCEPT
          ![fileID].openHandle.other.individual[client].read=(LateClock+leaseTime)
        ]
     /\ SendMessage(
          client,
          MakeSingletonLeaseGrantMessage(
            MakeFileOpenHandleField(fileID,BBOther),
            PRead,
            value,
            FALSE,
            LateClock+leaseTime))

(*Defn*)ExtendOpenHandleLease(client,fileID,so,rw)==
  LET
    (*Defn*)serverLeaseTimeRange==
      IF so=BBSelf/\ rw=PRead
      THEN
        ServerLongLeaseTimeRange
      ELSE
        ServerShortLeaseTimeRange
  IN
    \E leaseTime \in serverLeaseTimeRange:
       /\ LateClock+leaseTime>
          (FileProtectionTableState[fileID].openHandle[so].individual[client])[rw]
       /\ UNCHANGED FileValueTableState
       /\ (FileProtectionTableState')=
          [FileProtectionTableState EXCEPT
            ![fileID].openHandle[so].individual[client][rw]=(LateClock+leaseTime)
          ]
       /\ SendMessage(
            client,
            MakeSingletonLeaseGrantMessage(
              MakeFileOpenHandleField(fileID,so),rw,Nil,TRUE,LateClock+leaseTime))

(* ********** BonaFide lease grant partial actions ************************************************************************* *)

(* 
	There are no enabling conditions for these partial actions.  All preconditions
	must be established by the actions that make use of these partial actions.
 *)

(*Defn*)GrantBonaFideLease(client,fileID)==
  \E leaseTime \in ServerLongLeaseTimeRange:
     /\ UNCHANGED FileValueTableState
     /\ (FileProtectionTableState')=
        [FileProtectionTableState EXCEPT
          ![fileID].bonaFide.individual[client].read=(LateClock+leaseTime)
        ]
     /\ SendMessage(
          client,
          MakeSingletonLeaseGrantMessage(
            MakeFileBonaFideField(fileID),
            PRead,
            FileValueTableState[fileID].bonaFide[client],
            FALSE,
            LateClock+leaseTime))

(*Defn*)ExtendBonaFideLease(client,fileID)==
  \E leaseTime \in ServerLongLeaseTimeRange:
     /\ LateClock+leaseTime>
        FileProtectionTableState[fileID].bonaFide.individual[client].read
     /\ UNCHANGED FileValueTableState
     /\ (FileProtectionTableState')=
        [FileProtectionTableState EXCEPT
          ![fileID].bonaFide.individual[client].read=(LateClock+leaseTime)
        ]
     /\ SendMessage(
          client,
          MakeSingletonLeaseGrantMessage(
            MakeFileBonaFideField(fileID),PRead,Nil,TRUE,LateClock+leaseTime))

(* ********** Mode lease grant partial actions ***************************************************************************** *)

(* 
	There are no enabling conditions for these partial actions.  All preconditions
	must be established by the actions that make use of these partial actions.
 *)

(*Defn*)GrantModeWriteSelfLease(client,fileID,mode)==
  \E leaseTime \in ServerShortLeaseTimeRange:
     /\ UNCHANGED FileValueTableState
     /\ (FileProtectionTableState')=
        [FileProtectionTableState EXCEPT
          ![fileID].modes[mode].self.individual[client].write=(LateClock+leaseTime)
        ]
     /\ SendMessage(
          client,
          MakeSingletonLeaseGrantMessage(
            MakeFileModeField(fileID,mode,BBSelf),PWrite,Nil,FALSE,LateClock+leaseTime))

(*Defn*)GrantOrExtendModeReadOtherLease(client,fileID,mode,value)==
  LET
    (*Defn*)extension==
      ClientHasIndividualBBLease(
        client,FileProtectionTableState[fileID].modes[mode],BBOther,PRead)
  IN
    \E leaseTime \in ServerShortLeaseTimeRange:
       /\ ( extension=>
            LateClock+leaseTime>
            FileProtectionTableState[fileID].modes[mode].other.individual[client].read)
       /\ (FileValueTableState')=
          [FileValueTableState EXCEPT![fileID].modes[mode].other[client]=value]
       /\ (FileProtectionTableState')=
          [FileProtectionTableState EXCEPT
            ![fileID].modes[mode].other.individual[client].read=(LateClock+leaseTime)
          ]
       /\ SendMessage(
            client,
            MakeSingletonLeaseGrantMessage(
              MakeFileModeField(fileID,mode,BBOther),
              PRead,
              value,
              extension,
              LateClock+leaseTime))

(*Defn*)ExtendModeLease(client,fileID,mode,so,rw)==
  \E leaseTime \in ServerShortLeaseTimeRange:
     /\ LateClock+leaseTime>
        ((FileProtectionTableState[fileID].modes[mode])[so].individual[client])[rw]
     /\ UNCHANGED FileValueTableState
     /\ (FileProtectionTableState')=
        [FileProtectionTableState EXCEPT
          ![fileID].modes[mode][so].individual[client][rw]=(LateClock+leaseTime)
        ]
     /\ SendMessage(
          client,
          MakeSingletonLeaseGrantMessage(
            MakeFileModeField(fileID,mode,so),rw,Nil,TRUE,LateClock+leaseTime))

(* ********** Black-box lease recall partial actions *********************************************************************** *)

(*Defn*)RecallALeaseToHideClientOpenHandleValue(client,fileID,priority)==
  \/ ( \E otherClient \in Client:
          /\ otherClient#client
          /\ ClientHasIndividualBBLease(
               otherClient,FileProtectionTableState[fileID].openHandle,BBSelf,PWrite)
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendMessage(
               otherClient,
               MakeLeaseRecallMessage(
                 MakeFileOpenHandleField(fileID,BBSelf),PWrite,priority)))
  \/ ( \E otherClient \in Client:
          /\ otherClient#client
          /\ ClientHasIndividualBBLease(
               otherClient,FileProtectionTableState[fileID].openHandle,BBOther,PWrite)
          /\ (\neg ClientShieldedFromOtherOpenHandles(otherClient,fileID))
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendMessage(
               otherClient,
               MakeLeaseRecallMessage(
                 MakeFileOpenHandleField(fileID,BBOther),PRead,priority)))

(*Defn*)RecallALeaseToHideClientModeValue(client,fileID,mode,priority)==
  \/ ( \E otherClient \in Client:
          /\ otherClient#client
          /\ ClientHasIndividualBBLease(
               otherClient,FileProtectionTableState[fileID].modes[mode],BBSelf,PWrite)
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendMessage(
               otherClient,
               MakeLeaseRecallMessage(
                 MakeFileModeField(fileID,mode,BBSelf),PWrite,priority)))
  \/ ( \E otherClient \in Client:
          /\ otherClient#client
          /\ ClientHasIndividualBBLease(
               otherClient,FileProtectionTableState[fileID].modes[mode],BBOther,PWrite)
          /\ (\neg ClientShieldedFromOtherModes(otherClient,fileID,mode))
          /\ UNCHANGED FileValueTableState
          /\ UNCHANGED FileProtectionTableState
          /\ SendMessage(
               otherClient,
               MakeLeaseRecallMessage(
                 MakeFileModeField(fileID,mode,BBOther),PRead,priority)))

(* ********** Path lease partial actions *********************************************************************************** *)

(*Defn*)GrantPathWarrant(client,fileID)==
  \E leaseTime \in ServerShortLeaseTimeRange:
     LET
       (*Defn*)maxDurationOfUpPathLease==
         FileProtectionTableState[fileID].path.up-EarlyClock
       (*Defn*)maxGrowthInTimeRange==maxDurationOfUpPathLease*MaxClockRateError
       (*Defn*)currentTimeRange==LateClock-EarlyClock
       (*Defn*)projectedTimeRange==currentTimeRange+maxGrowthInTimeRange
       (*Defn*)guardedExpiration==
         FileProtectionTableState[fileID].path.up-projectedTimeRange
       (*Defn*)expiration==MinElement({LateClock+leaseTime,guardedExpiration})
     IN
       /\ UNCHANGED FileValueTableState
       /\ (FileProtectionTableState')=
          [FileProtectionTableState EXCEPT
            ![fileID].path.individual[client].read=expiration
          ]
       /\ SendMessage(
            client,
            MakeSingletonLeaseGrantMessage(
              MakeFilePathField(fileID),
              PRead,
              FileValueTableState[fileID].path,
              FALSE,
              expiration))

(*Defn*)ExtendPathWarrant(client,fileID)==
  \E leaseTime \in ServerShortLeaseTimeRange:
     LET
       (*Defn*)maxDurationOfUpPathLease==
         FileProtectionTableState[fileID].path.up-EarlyClock
       (*Defn*)maxGrowthInTimeRange==maxDurationOfUpPathLease*MaxClockRateError
       (*Defn*)currentTimeRange==LateClock-EarlyClock
       (*Defn*)projectedTimeRange==currentTimeRange+maxGrowthInTimeRange
       (*Defn*)guardedExpiration==
         FileProtectionTableState[fileID].path.up-projectedTimeRange
       (*Defn*)expiration==MinElement({LateClock+leaseTime,guardedExpiration})
     IN
       /\ expiration>FileProtectionTableState[fileID].path.individual[client].read
       /\ UNCHANGED FileValueTableState
       /\ (FileProtectionTableState')=
          [FileProtectionTableState EXCEPT
            ![fileID].path.individual[client].read=expiration
          ]
       /\ SendMessage(
            client,
            MakeSingletonLeaseGrantMessage(
              MakeFilePathField(fileID),PRead,Nil,TRUE,expiration))

(*Defn*)GrantOrExtendPathLease(fileID,label)==
  \E leaseTime \in ServerShortLeaseTimeRange:
     LET
       (*Defn*)extension==DownPathLeaseIssued(fileID,label)
       (*Defn*)childFile==FileValueTableState[fileID].children[label]
       (*Defn*)ancestors==Append(FileValueTableState[fileID].path,fileID)
       (*Defn*)expiration==
         MinElement({LateClock+leaseTime,FileProtectionTableState[fileID].path.up})
     IN
       \E server \in Server:
          /\ ServerOwnsFile(server,childFile)
          /\ (extension=>expiration>FileProtectionTableState[fileID].path.down[label])
          /\ IF server#thisHost
             THEN
               /\ UNCHANGED FileValueTableState
               /\ (FileProtectionTableState')=
                  [FileProtectionTableState EXCEPT![fileID].path.down[label]=expiration]
               /\ SendMessage(
                    server,
                    MakePathGrantMessage(
                      childFile,fileID,IF extension THEN<<>>ELSE ancestors,extension,expiration))
             ELSE IF
               \A client \in Client:(\neg ClientHasWriteSVLease(client,childFile,FParent))
             THEN
               /\ (FileValueTableState')=
                  IF extension
                  THEN
                    FileValueTableState
                  ELSE
                    [FileValueTableState EXCEPT![childFile].path=ancestors]
               /\ (FileProtectionTableState')=
                  [FileProtectionTableState EXCEPT
                    ![fileID].path.down[label]=expiration,![childFile].path.up=expiration
                  ]
               /\ SendNoMessage
             ELSE
               /\ UNCHANGED FileValueTableState
               /\ UNCHANGED FileProtectionTableState
               /\ SendNoMessage

(* This partial action will be FALSE if rootFile has no path leases issued or path warrants granted *)

(*Defn*)RecallAllPathLeasesAndWarrants(rootFile,priority)==
  \E fileID \in FileID:
     /\ ServerOwnsFile(thisHost,fileID)
     /\ UpPathLeaseObtained(fileID)
     /\ UNCHANGED FileValueTableState
     /\ ( \/ ( \E server \in Server:
                  LET
                    (*Defn*)parentFile==FileValueTableState[fileID].parent.fileID
                    (*Defn*)parentLabel==FileValueTableState[fileID].parent.label
                    (*Defn*)expiration==FileProtectionTableState[fileID].path.up
                  IN
                    /\ IsElementInSeq(rootFile,FileValueTableState[fileID].path.up)
                    /\ (\A label \in Label:(\neg DownPathLeaseIssued(fileID,label)))
                    /\ (\A client \in Client:(\neg ClientHasPathWarrant(client,fileID)))
                    /\ ServerOwnsFile(server,parentFile)
                    /\ IF server=thisHost
                       THEN
                         /\ (FileProtectionTableState')=
                            [FileProtectionTableState EXCEPT
                              ![fileID].path.up=BeforeTimeBegins,
                              ![parentFile].path.down[parentLabel]=BeforeTimeBegins
                            ]
                         /\ SendNoMessage
                       ELSE
                         /\ (FileProtectionTableState')=
                            [FileProtectionTableState EXCEPT![fileID].path.up=BeforeTimeBegins]
                         /\ SendMessage(server,MakePathReleaseMessage(parentFile,fileID,expiration)))
          \/ ( \E label \in Label,server \in Server:
                  LET
                    (*Defn*)childFile==FileValueTableState[fileID].children[label]
                  IN
                    /\ ( \/ fileID=rootFile
                         \/ IsElementInSeq(rootFile,FileValueTableState[fileID].path))
                    /\ DownPathLeaseIssued(fileID,label)
                    /\ ServerOwnsFile(server,childFile)
                    /\ server#thisHost
                    /\ UNCHANGED FileProtectionTableState
                    /\ SendMessage(server,MakePathRecallMessage(childFile,fileID,priority)))
          \/ ( \E client \in Client:
                  /\ ( \/ fileID=rootFile
                       \/ IsElementInSeq(rootFile,FileValueTableState[fileID].path))
                  /\ ClientHasPathWarrant(client,fileID)
                  /\ UNCHANGED FileProtectionTableState
                  /\ SendMessage(
                       client,MakeLeaseRecallMessage(MakeFilePathField(fileID),PRead,priority))))

(*Defn*)RecallPathLease(fileID,label,priority)==
  LET
    (*Defn*)childFile==FileValueTableState[fileID].children[label]
  IN
    \E server \in Server:
       /\ ServerOwnsFile(server,childFile)
       /\ IF server#thisHost
          THEN
            /\ UNCHANGED FileValueTableState
            /\ UNCHANGED FileProtectionTableState
            /\ SendMessage(server,MakePathRecallMessage(childFile,fileID,priority))
          ELSE IF
            /\ (\A childLabel \in Label:(\neg DownPathLeaseIssued(childFile,childLabel)))
            /\ (\A client \in Client:(\neg ClientHasPathWarrant(client,childFile)))
          THEN
            /\ UNCHANGED FileValueTableState
            /\ (FileProtectionTableState')=
               [FileProtectionTableState EXCEPT
                 ![fileID].path.down[label]=BeforeTimeBegins,
                 ![childFile].path.up=BeforeTimeBegins
               ]
            /\ SendNoMessage
          ELSE
            RecallAllPathLeasesAndWarrants(childFile,priority)

(*Defn*)ReleasePathLease(fileID,priority)==
  LET
    (*Defn*)parentFile==FileValueTableState[fileID].parent.fileID
    (*Defn*)parentLabel==FileValueTableState[fileID].parent.label
    (*Defn*)expiration==FileProtectionTableState[fileID].path.up
  IN
    \E server \in Server:
       /\ ServerOwnsFile(server,parentFile)
       /\ IF
            \/ (\E label \in Label:DownPathLeaseIssued(fileID,label))
            \/ (\E client \in Client:ClientHasPathWarrant(client,fileID))
          THEN
            RecallAllPathLeasesAndWarrants(fileID,priority)
          ELSE IF server=thisHost
          THEN
            /\ UNCHANGED FileValueTableState
            /\ (FileProtectionTableState')=
               [FileProtectionTableState EXCEPT
                 ![fileID].path.up=BeforeTimeBegins,
                 ![parentFile].path.down[parentLabel]=BeforeTimeBegins
               ]
            /\ SendNoMessage
          ELSE
            /\ UNCHANGED FileValueTableState
            /\ (FileProtectionTableState')=
               [FileProtectionTableState EXCEPT![fileID].path.up=BeforeTimeBegins]
            /\ SendMessage(server,MakePathReleaseMessage(parentFile,fileID,expiration))
====
