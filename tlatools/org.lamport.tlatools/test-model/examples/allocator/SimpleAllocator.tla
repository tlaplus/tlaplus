------------------------ MODULE SimpleAllocator -------------------------
(***********************************************************************)
(* Specification of an allocator managing a set of resources:          *)
(* - Clients can request sets of resources whenever all their previous *)
(*   requests have been satisfied.                                     *)
(* - Requests can be partly fulfilled, and resources can be returned   *)
(*   even before the full request has been satisfied. However, clients *)
(*   only have an obligation to return resources after they have       *)
(*   obtained all resources they requested.                            *)
(***********************************************************************)

EXTENDS FiniteSets, TLC

CONSTANTS
  Clients,     \* set of all clients
  Resources    \* set of all resources

ASSUME
  IsFiniteSet(Resources)

VARIABLES
  unsat,       \* set of all outstanding requests per process
  alloc        \* set of resources allocated to given process

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

-------------------------------------------------------------------------

(* Resources are available iff they have not been allocated. *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

(* Initially, no resources have been requested or allocated. *)
Init == 
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

(* A client c may request a set of resources provided that all of its  *)
(* previous requests have been satisfied and that it doesn't hold any  *)
(* resources.                                                          *)
Request(c,S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {} /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

(* Allocation of a set of available resources to a client that         *)
(* requested them (the entire request does not have to be filled).     *)
Allocate(c,S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* Client c returns a set of resources that it holds. It may do so     *)
(* even before its full request has been honored.                      *)
Return(c,S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

(* The next-state relation. *)
Next == 
  \E c \in Clients, S \in SUBSET Resources :
     Request(c,S) \/ Allocate(c,S) \/ Return(c,S)

vars == <<unsat,alloc>>

-------------------------------------------------------------------------

(* The complete high-level specification. *)
SimpleAllocator == 
  /\ Init /\ [][Next]_vars
  /\ \A c \in Clients: WF_vars(Return(c, alloc[c]))
  /\ \A c \in Clients: SF_vars(\E S \in SUBSET Resources: Allocate(c,S))

-------------------------------------------------------------------------

ResourceMutex ==
  \A c1,c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

ClientsWillReturn ==
  \A c \in Clients : unsat[c]={} ~> alloc[c]={}

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : r \in unsat[c] ~> r \in alloc[c]

InfOftenSatisfied == 
  \A c \in Clients : []<>(unsat[c] = {})

-------------------------------------------------------------------------

(* Used for symmetry reduction with TLC *)
Symmetry == Permutations(Clients) \cup Permutations(Resources)

-------------------------------------------------------------------------

(* The following version states a weaker fairness requirement for the  *)
(* clients: resources need be returned only if the entire request has  *)
(* been satisfied.                                                     *)

SimpleAllocator2 == 
  /\ Init /\ [][Next]_vars
  /\ \A c \in Clients: WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients: SF_vars(\E S \in SUBSET Resources: Allocate(c,S))


-------------------------------------------------------------------------

THEOREM SimpleAllocator => []TypeInvariant
THEOREM SimpleAllocator => []ResourceMutex
THEOREM SimpleAllocator => ClientsWillReturn
THEOREM SimpleAllocator2 => ClientsWillReturn
THEOREM SimpleAllocator => ClientsWillObtain
THEOREM SimpleAllocator => InfOftenSatisfied
(** The following do not hold:                          **)
(** THEOREM SimpleAllocator2 => ClientsWillObtain       **)
(** THEOREM SimpleAllocator2 => InfOftenSatisfied       **)
=========================================================================
