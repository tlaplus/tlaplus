---- MODULE HostBaseModule ----
(*`^\addcontentsline{toc}{section}{HostBaseModule}^'*)

EXTENDS
  MessageOrderDependencyModule,
  ClockSyncPortalModule,
  MessengerPortalModule,
  CertifierPortalModule
CONSTANT thisHost
====
