---- MODULE PhysicalComponentsModule ----
(*`^\addcontentsline{toc}{section}{PhysicalComponentsModule}^'*)

EXTENDS
  Stubs,
  Naturals,
  Integers,
  Reals,
  Sequences,
  AdditionalSequenceOperators,
  AdditionalMathOperators
CONSTANT Client

CONSTANT Server

CONSTANT Machine

(*  machine identities don't show up in spec, but we need a constant
	to supply to constructors.  *)

CONSTANT DummyMachine

ASSUME DummyMachine \in Machine

CONSTANT Blob

(*Defn*)ClientOrNil==NilOr(Client)

(*Defn*)BlobSet==SUBSET Blob

(*Defn*)BlobSeq==ArbSeq(Blob)

(*Defn*)ServerSet==SUBSET Server

ASSUME Nil \notin Client

ASSUME Nil \notin Server

ASSUME Nil \notin Blob

ASSUME Client \intersect Server={}

(*Defn*)Host==Client \union Server

(*Defn*)RootServer==CHOOSE server:server \in Server

(*Defn*)BeforeTimeBegins==0-Infinity

(*Defn*)BeginningOfTime==0

(*Defn*)AfterTimeEnds==Infinity

(*Defn*)ClosedTime==Nat \union{BeforeTimeBegins,AfterTimeEnds}

(*Defn*)OpenTime==Nat

(*Defn*)TimeOffset==Int

(*Defn*)Duration==Nat

(* 
	The rate of each host's base clock has a relative error no greater than
	MaxClockRateError.  This value is used by the ClockSync module when
	advancing host clocks, and it is also used by the GrantPathWarrant
	partial action in the ServerLeasePartialActions module when computing
	the expiration time of a path warrant.
 *)

CONSTANT MaxClockRateError

ASSUME MaxClockRateError \in Real

ASSUME MaxClockRateError \geq 0

(* 
	When a client creates a new fileID, it can give itself leases on the fileID.
	If the lease expiration time is no more than ClientLeaseTimeLimit in the
	future, then the server will accept it.

	If a client sets a black-box self value to a time that is no more than
	BBSelfTimeLimit beyond the expiration time of the writeSelf protection,
	then the server will accept it.
 *)

CONSTANT ClientShortLeaseTimeLimit

CONSTANT ClientLongLeaseTimeLimit

ASSUME ClientShortLeaseTimeLimit \in Duration

ASSUME ClientLongLeaseTimeLimit \in Duration

CONSTANT ServerMinShortLeaseTime

CONSTANT ServerMaxShortLeaseTime

CONSTANT ServerMinLongLeaseTime

CONSTANT ServerMaxLongLeaseTime

ASSUME ServerMinShortLeaseTime \in Duration

ASSUME ServerMaxShortLeaseTime \in Duration

ASSUME ServerMinLongLeaseTime \in Duration

ASSUME ServerMaxLongLeaseTime \in Duration

ASSUME ServerMinShortLeaseTime \leq ServerMaxShortLeaseTime

ASSUME ServerMinLongLeaseTime \leq ServerMaxLongLeaseTime

ASSUME ServerMinShortLeaseTime \leq ServerMinLongLeaseTime

ASSUME ServerMaxShortLeaseTime \leq ServerMaxLongLeaseTime

(*Defn*)ServerShortLeaseTimeRange==
  ServerMinShortLeaseTime..ServerMaxShortLeaseTime

(*Defn*)ServerLongLeaseTimeRange==
  ServerMinLongLeaseTime..ServerMaxLongLeaseTime

CONSTANT ServerMinInterlockTime

CONSTANT ServerMaxInterlockTime

ASSUME ServerMinInterlockTime \in Duration

ASSUME ServerMaxInterlockTime \in Duration

ASSUME ServerMinInterlockTime \leq ServerMaxInterlockTime

(*Defn*)ServerInterlockTimeRange==
  ServerMinInterlockTime..ServerMaxInterlockTime
====
