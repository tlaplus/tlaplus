---- MODULE DistributedSystemModule ----
(*`^\addcontentsline{toc}{section}{DistributedSystemModule}^'*)

EXTENDS
  AbstractComponentsModule,
  PhysicalComponentsModule,
  ClockSyncModule,
  MessengerModule,
  CertifierModule,
  ServerCreatorModule
VARIABLE distributedState

ClientHost(host)==
  INSTANCE ClientModule WITH
    ActionSerialNumber<-distributedState[host].ActionSerialNumber,
    ThreadTable<-distributedState[host].ThreadTable,
    FileValueTableState<-distributedState[host].FileValueTableState,
    ActiveProtectionRecords<-distributedState[host].ActiveProtectionRecords,
    MessageLog<-distributedState[host].MessageLog,
    LeaseRecallMessageBuffer<-distributedState[host].LeaseRecallMessageBuffer,
    Corrupted<-distributedState[host].Corrupted,
    FileMap<-distributedState[host].FileMap,
    ActiveBorrowerRecords<-distributedState[host].ActiveBorrowerRecords,
    BaseClock<-(HostBaseClocks[host]),
    EarlyOffset<-(HostEarlyOffsets[host]),
    LateOffset<-(HostLateOffsets[host]),
    AddressedMessageSetToSend<-(HostAddressedMessageSetsToSend[host]),
    MessageReceiptDecision<-(HostMessageReceiptDecisions[host]),
    IncomingMessageQueues<-(HostIncomingMessageQueues[host]),
    CertificateSetToSign<-(HostCertificateSetsToSign[host]),
    thisHost<-host

ServerHost(host)==
  INSTANCE ServerModule WITH
    FileValueTableState<-distributedState[host].FileValueTableState,
    FileProtectionTableState<-distributedState[host].FileProtectionTableState,
    ConsistencyMessageBuffer<-distributedState[host].ConsistencyMessageBuffer,
    LeaseRequestMessageBuffer<-distributedState[host].LeaseRequestMessageBuffer,
    InterlockMessageBuffer<-distributedState[host].InterlockMessageBuffer,
    Corrupted<-distributedState[host].Corrupted,
    OwnershipAuthorizingServer
      <-distributedState[host].OwnershipAuthorizingServer,
    IssuedDeeds<-distributedState[host].IssuedDeeds,
    FileMap<-distributedState[host].FileMap,
    ActiveBorrowerRecords<-distributedState[host].ActiveBorrowerRecords,
    BaseClock<-(HostBaseClocks[host]),
    EarlyOffset<-(HostEarlyOffsets[host]),
    LateOffset<-(HostLateOffsets[host]),
    AddressedMessageSetToSend<-(HostAddressedMessageSetsToSend[host]),
    MessageReceiptDecision<-(HostMessageReceiptDecisions[host]),
    IncomingMessageQueues<-(HostIncomingMessageQueues[host]),
    CertificateSetToSign<-(HostCertificateSetsToSign[host]),
    ServerToConceive<-(ServerServersToConceive[host]),
    Birthday<-(ServerBirthdays[host]),
    ParentServer<-(ServerParentServers[host]),
    thisHost<-host

(*Defn*)Init==
  /\ (\A client \in Client:ClientHost(client)!Init)
  /\ (\A server \in Server:ServerHost(server)!Init)
  /\ ClockSyncInitialized
  /\ MessengerInitialized
  /\ CertifierInitialized
  /\ ServerCreationInitialized

(*Defn*)Next==
  /\ UpdateHostClocks
  /\ UpdateMessageQueues
  /\ UpdateSignedCertificates
  /\ UpdateServerExistence
  /\ ( \/ ( \E activeClient \in Client:
               /\ ClientHost(activeClient)!Next
               /\ (\A client \in Client:client#activeClient=>ClientHost(client)!DoNothing)
               /\ (\A server \in Server:ServerHost(server)!DoNothing))
       \/ ( \E activeServer \in Server:
               /\ IF activeServer \in AliveServers
                  THEN
                    ServerHost(activeServer)!Next
                  ELSE
                    ServerHost(activeServer)!ComeIntoExistence
               /\ (\A client \in Client:ClientHost(client)!DoNothing)
               /\ (\A server \in Server:server#activeServer=>ServerHost(server)!DoNothing)))
====
