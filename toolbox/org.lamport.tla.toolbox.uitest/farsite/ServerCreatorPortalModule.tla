---- MODULE ServerCreatorPortalModule ----
(*`^\addcontentsline{toc}{section}{ServerCreatorPortalModule}^'*)

EXTENDS PhysicalComponentsModule
VARIABLE ServerToConceive

VARIABLE Birthday

VARIABLE ParentServer

VARIABLE ConceivedServers

(*Defn*)InitiateCreationOfDelegateServer(server)==
  /\ server \notin ConceivedServers
  /\ (ServerToConceive')=server
  /\ (Birthday')=FALSE

(*Defn*)CompleteCreationOfThisServer(parent)==
  /\ ParentServer=parent
  /\ (ServerToConceive')=Nil
  /\ (Birthday')=TRUE

(*Defn*)NoChangeToServerExistence==
  /\ (ServerToConceive')=Nil
  /\ (Birthday')=FALSE
====
