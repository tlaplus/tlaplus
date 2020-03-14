---- MODULE ClockSyncModule ----
(*`^\addcontentsline{toc}{section}{ClockSyncModule}^'*)

EXTENDS PhysicalComponentsModule
(* ********** Definitions ************************************************************************************************** *)

(*Defn*)SynchInfo==[earlyTime:OpenTime,lateTime:OpenTime]

(*Defn*)NoSynchInfo==[earlyTime:{BeforeTimeBegins},lateTime:{AfterTimeEnds}]

(*Defn*)HostSynchInfoType==[Host->SynchInfo \union NoSynchInfo]

(*Defn*)HostBaseClocksType==[Host->OpenTime]

(*Defn*)HostClockOffsetType==[Host->TimeOffset]

VARIABLE ReferenceClock

VARIABLE HostBaseClocks

VARIABLE HostEarlyOffsets

VARIABLE HostLateOffsets

(*Defn*)ReferenceClockType==OpenTime

(*Defn*)HostEarlyOffsetsType==HostClockOffsetType

(*Defn*)HostLateOffsetsType==HostClockOffsetType

(*Theorem   `^\addcontentsline{toc}{subsection}{}^'*)
THEOREM
  \A host \in Host:
     /\ HostBaseClocks[host]+HostEarlyOffsets[host]\leq ReferenceClock
     /\ HostBaseClocks[host]+HostLateOffsets[host]\geq ReferenceClock
  (*Reasoning:*)

(**)

(**)

(* ********** Predicates *************************************************************************************************** *)

(*Defn*)ClockSyncInitialized==
  /\ ReferenceClock=BeginningOfTime
  /\ HostBaseClocks \in HostBaseClocksType
  /\ HostEarlyOffsets \in HostClockOffsetType
  /\ HostLateOffsets \in HostClockOffsetType

(* ********** Actions ****************************************************************************************************** *)

(*Defn*)UpdateHostClocks==
  \E newReferenceClock \in OpenTime,
     hostSynchInfo \in HostSynchInfoType,
     newHostBaseClocks \in HostBaseClocksType,
     newHostEarlyOffsets \in HostClockOffsetType,
     newHostLateOffsets \in HostClockOffsetType
     :
     /\ newReferenceClock \geq ReferenceClock
     /\ ( \A host \in Host:
             LET
               (*Defn*)elapsedTime==newReferenceClock-ReferenceClock
               (*Defn*)hostElapsedTime==newHostBaseClocks[host]-HostBaseClocks[host]
               (*Defn*)maxDrift==hostElapsedTime*MaxClockRateError
             IN
               /\ hostSynchInfo[host].earlyTime \leq newReferenceClock
               /\ hostSynchInfo[host].lateTime \geq newReferenceClock
               /\ newHostBaseClocks[host]\geq HostBaseClocks[host]
               /\ hostElapsedTime \leq elapsedTime*(1+MaxClockRateError)
               /\ hostElapsedTime \geq elapsedTime*(1-MaxClockRateError)
               /\ newHostEarlyOffsets[host]=
                  MaxElement(
                    {
                    HostEarlyOffsets[host]-maxDrift,
                    hostSynchInfo[host].earlyTime-newHostBaseClocks[host]
                    })
               /\ newHostLateOffsets[host]=
                  MinElement(
                    {
                    HostLateOffsets[host]+maxDrift,
                    hostSynchInfo[host].lateTime-newHostBaseClocks[host]
                    }))
     /\ (ReferenceClock')=newReferenceClock
     /\ (HostBaseClocks')=newHostBaseClocks
     /\ (HostEarlyOffsets')=newHostEarlyOffsets
     /\ (HostLateOffsets')=newHostLateOffsets
====
