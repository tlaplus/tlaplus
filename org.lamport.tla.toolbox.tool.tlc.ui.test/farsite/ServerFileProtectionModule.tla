---- MODULE ServerFileProtectionModule ----
(*`^\addcontentsline{toc}{section}{ServerFileProtectionModule}^'*)

EXTENDS HostBaseModule,ServerCreatorPortalModule
(* ********** Basic Lease Protections ************************************************************************************** *)

(*Defn*)ReadWriteProtections==[read:ClosedTime,write:ClosedTime]

(*Defn*)ReadOnlyProtections==[read:ClosedTime]

(*Defn*)WriteOnlyProtections==[write:ClosedTime]

(* ********** Shared-Value Leases ****************************************************************************************** *)

(*Defn*)SharedValues==UNION{Content,Boolean,Parent,NilOr(FileID)}

(*  following struct a lazy hack for the generated code.
<Definition>
	Reservations ==
	  [	client : NilOr(Client),
		leader : NilOr(FileID),
		value : SharedValues
	  ]
</Definition>
TODO should de-pluralize Reservations, and decide how
to handle SharedValues. Here I'm sloppy and use FileValueType, which is
a superset of SharedValues.  *)

(*Defn*)Reservations==
  [client:ClientOrNil,leader:FileOrNil,value:FileValueType]
(*Defn*)MakeReservations(i_client,i_leader,i_value)==
  [client|->i_client,leader|->i_leader,value|->i_value]

(*Defn*)Reservation(client,leader,value)==
  [client|->client,leader|->leader,value|->value]

(*Defn*)SVIndividuals==[Client->ReadWriteProtections]

(*Defn*)SVEveryones==ReadOnlyProtections

(*Defn*)SharedValueLeases==
  [individual:SVIndividuals,everyone:SVEveryones,reservation:Reservations]

(* ********** Child Shared-Value Leases ************************************************************************************ *)

(*Defn*)SingletonChildren==[Label->SharedValueLeases]

(*Defn*)InfiniteChildren==
  [excludedLabels:LabelSet,client:NilOr(Client),write:ClosedTime]

(*Defn*)InfiniteChild(excludedLabels,client,write)==
  [excludedLabels|->excludedLabels,client|->client,write|->write]

(*Defn*)Children==[singleton:SingletonChildren,infinite:InfiniteChildren]

(*Defn*)BlackBoxValues==UNION{HandleSet,Boolean}

(* ********** Black-Box Leases ********************************************************************************************* *)

(*Defn*)BBIndependentSelves==
  [individual:[Client->ReadWriteProtections],everyone:ReadWriteProtections]

(*Defn*)BBDependentSelves==
  [individual:[Client->WriteOnlyProtections],everyone:ReadWriteProtections]

(*Defn*)BBOthers==
  [individual:[Client->ReadOnlyProtections],everyone:ReadOnlyProtections]

(*Defn*)BlackBoxIndependentLeases==[self:BBIndependentSelves,other:BBOthers]

(*Defn*)BlackBoxDependentLeases==[self:BBDependentSelves,other:BBOthers]

(* ********** Private-Value Leases ***************************************************************************************** *)

(*Defn*)PrivateValueLeases==
  [individual:[Client->ReadOnlyProtections],everyone:ReadOnlyProtections]

(* ********** Path Leases and Warrants ************************************************************************************* *)

(*Defn*)PathLeases==
  [
    up:ClosedTime,
    down:[Label->ClosedTime],
    individual:[Client->ReadOnlyProtections]
  ]

(* ********** FileProtection ********************************************************************************************** *)

(*Defn*)FileProtection==
  [
    content:SharedValueLeases,
    delDisp:SharedValueLeases,
    parent:SharedValueLeases,
    children:Children,
    openHandle:BlackBoxIndependentLeases,
    bonaFide:PrivateValueLeases,
    modes:[Mode->BlackBoxDependentLeases],
    path:PathLeases,
    maxSuffix:Nat
  ]

(* ********** FileProtectionTableState ****************************************************************************************** *)

(*Defn*)FileProtectionTables==[FileID->FileProtection]

VARIABLE FileProtectionTableState

(*Defn*)FileProtectionTableStateType==FileProtectionTables

(* ********** Initialization *********************************************************************************************** *)

(*Defn*)FileProtectionInit==
  CHOOSE fileProtection \in FileProtection:
    ( \A client \in Client,label \in Label,mode \in Mode,access \in Access:
         /\ fileProtection.content.individual[client].read=BeforeTimeBegins
         /\ fileProtection.content.individual[client].write=BeforeTimeBegins
         /\ fileProtection.content.everyone.read=BeforeTimeBegins
         /\ fileProtection.content.reservation=Reservation(Nil,Nil,Nil)
         /\ fileProtection.delDisp.individual[client].read=BeforeTimeBegins
         /\ fileProtection.delDisp.individual[client].write=BeforeTimeBegins
         /\ fileProtection.delDisp.everyone.read=BeforeTimeBegins
         /\ fileProtection.delDisp.reservation=Reservation(Nil,Nil,Nil)
         /\ fileProtection.parent.individual[client].read=BeforeTimeBegins
         /\ fileProtection.parent.individual[client].write=BeforeTimeBegins
         /\ fileProtection.parent.everyone.read=BeforeTimeBegins
         /\ fileProtection.parent.reservation=Reservation(Nil,Nil,MakeParent(Nil,Nil))
         /\ fileProtection.children.singleton[label].individual[client].read=
            BeforeTimeBegins
         /\ fileProtection.children.singleton[label].individual[client].write=
            BeforeTimeBegins
         /\ fileProtection.children.singleton[label].everyone.read=BeforeTimeBegins
         /\ fileProtection.children.singleton[label].reservation=Reservation(Nil,Nil,Nil)
         /\ fileProtection.children.infinite=InfiniteChild({},Nil,BeforeTimeBegins)
         /\ fileProtection.openHandle.self.individual[client].read=BeforeTimeBegins
         /\ fileProtection.openHandle.self.individual[client].write=BeforeTimeBegins
         /\ fileProtection.openHandle.self.everyone.read=BeforeTimeBegins
         /\ fileProtection.openHandle.self.everyone.write=BeforeTimeBegins
         /\ fileProtection.openHandle.other.individual[client].read=BeforeTimeBegins
         /\ fileProtection.openHandle.other.everyone.read=BeforeTimeBegins
         /\ fileProtection.bonaFide.individual[client].read=BeforeTimeBegins
         /\ fileProtection.bonaFide.everyone.read=BeforeTimeBegins
         /\ fileProtection.modes[mode].self.individual[client].write=BeforeTimeBegins
         /\ fileProtection.modes[mode].self.everyone.write=BeforeTimeBegins
         /\ fileProtection.modes[mode].other.individual[client].read=BeforeTimeBegins
         /\ fileProtection.modes[mode].other.everyone.read=BeforeTimeBegins
         /\ fileProtection.path.up=BeforeTimeBegins
         /\ fileProtection.path.down[label]=BeforeTimeBegins
         /\ fileProtection.path.individual[client].read=BeforeTimeBegins
         /\ fileProtection.maxSuffix=0)

(*Defn*)FileProtectionRootInit==
  [
    [
      [FileProtectionInit EXCEPT
        !.openHandle=
          [@EXCEPT
            !.self=
              [@EXCEPT
                !.individual=
                  [client \in DOMAIN@|->
                    IF client \in Client
                    THEN
                      LET(*Defn*)AtSymbol001==@[client]IN[AtSymbol001 EXCEPT!.read=AfterTimeEnds]
                    ELSE
                      @[client]
                  ]
              ]
          ]
      ]
    EXCEPT
      !.bonaFide=
        [@EXCEPT
          !.individual=
            [client \in DOMAIN@|->
              IF client \in Client
              THEN
                LET(*Defn*)AtSymbol002==@[client]IN[AtSymbol002 EXCEPT!.read=AfterTimeEnds]
              ELSE
                @[client]
            ]
        ]
    ]
  EXCEPT
    !.path.up=AfterTimeEnds
  ]

(*Defn*)FileProtectionTableInit==
  [fileID \in FileID|->
    IF fileID=FilesystemRoot THEN FileProtectionRootInit ELSE FileProtectionInit
  ]
====
