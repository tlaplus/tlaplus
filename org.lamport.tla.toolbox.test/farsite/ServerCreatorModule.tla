---- MODULE ServerCreatorModule ----
(*`^\addcontentsline{toc}{section}{ServerCreatorModule}^'*)

EXTENDS PhysicalComponentsModule
(*Defn*)ServerServersToConceiveType==[Server->NilOr(Server)]

(*Defn*)ServerBirthdaysType==[Server->Boolean]

(*Defn*)ServerParentServersType==[Server->NilOr(Server)]

(*Defn*)ConceivedServersType==ServerSet

(*Defn*)AliveServersType==ServerSet

(*Defn*)ServerServersToConceiveInit==[server \in Server|->Nil]

(*Defn*)ServerBirthdaysInit==[server \in Server|->FALSE]

(*Defn*)ServerParentServersInit==[server \in Server|->Nil]

(*Defn*)ConceivedServersInit=={RootServer}

(*Defn*)AliveServersInit=={RootServer}

VARIABLE ServerServersToConceive

VARIABLE ServerBirthdays

VARIABLE ServerParentServers

VARIABLE ConceivedServers

VARIABLE AliveServers

(* ********** Predicates *************************************************************************************************** *)

(*Defn*)ServerCreationInitialized==
  /\ ServerServersToConceive=ServerServersToConceiveInit
  /\ ServerParentServers=ServerParentServersInit
  /\ ServerBirthdays=ServerBirthdaysInit
  /\ ConceivedServers=ConceivedServersInit
  /\ AliveServers=AliveServersInit

(* ********** Actions ****************************************************************************************************** *)

(*Defn*)UpdateServerExistence==
  \E serverServersToConceive \in ServerServersToConceiveType,
     serverBirthdays \in ServerBirthdaysType
     :
     /\ (ServerServersToConceive')=serverServersToConceive
     /\ (ServerBirthdays')=serverBirthdays
     /\ (ServerParentServers')=
        [server \in Server|->
          IF
            /\ server \notin ConceivedServers
            /\ ( \E parentServer \in AliveServers:serverServersToConceive[parentServer]=server)
          THEN
            CHOOSE parentServer \in AliveServers:
              serverServersToConceive[parentServer]=server
          ELSE
            ServerParentServers[server]
        ]
     /\ (ConceivedServers')=
        ConceivedServers \union
        ( {server \in Server:
            ( \E parentServer \in AliveServers:serverServersToConceive[parentServer]=server)
          })
     /\ (AliveServers')=
        AliveServers \union({server \in ConceivedServers:(serverBirthdays[server])})
====
