------------------------ MODULE SchedulingAllocator ---------------------
(***********************************************************************)
(* Specification of an allocator managing a set of resources:          *)
(* - Clients can request sets of resources whenever all their previous *)
(*   requests have been satisfied.                                     *)
(* - Requests can be partly fulfilled, and resources can be returned   *)
(*   even before the full request has been satisfied. However, clients *)
(*   only have an obligation to return resources after they have       *)
(*   obtained all resources they requested.                            *)
(* This allocator operates by repeatedly choosing a schedule according *)
(* to which requests are satisfied. Resources can be allocated out of  *)
(* order as long as no client earlier in the schedule asks for them.   *)
(***********************************************************************)

EXTENDS FiniteSets, Sequences, Naturals, TLC

CONSTANTS
  Clients,     \* set of all clients
  Resources    \* set of all resources

ASSUME
  IsFiniteSet(Resources)

VARIABLES
  unsat,       \* set of all outstanding requests per process
  alloc,       \* set of resources allocated to given process
  sched        \* schedule represented as a sequence of clients


TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

-------------------------------------------------------------------------

(* The set of permutations of a finite set, represented as sequences.  *)
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
       IF ss = {} THEN { << >> }
       ELSE LET ps == [ x \in ss |-> 
                        { Append(sq,x) : sq \in perms[ss \ {x}] } ]
            IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

(* Remove element at index i from a sequence.                          *)
(* Assumes that i \in 1..Len(seq)                                      *)
Drop(seq,i) == SubSeq(seq, 1, i-1) \circ SubSeq(seq, i+1, Len(seq))

(* Resources are available iff they have not been allocated. *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

(* Range of a function, e.g. elements of a sequence *)
Range(f) == { f[x] : x \in DOMAIN f }

(* Clients with pending requests that have not yet been scheduled *)
toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

(* Initially, no resources have been requested or allocated. *)
Init == 
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

(* A client c may request a set of resources provided that all of its  *)
(* previous requests have been satisfied and that it doesn't hold any  *)
(* resources. The client is added to the pool of clients with          *)
(* outstanding requests.                                               *)
Request(c,S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {} /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc,sched>>

(* Allocation of a set of available resources to a client that has     *)
(* requested them (the entire request does not have to be filled).     *)
(* The process must appear in the schedule, and no process earlier in  *)
(* the schedule may have requested one of the resources.               *)
Allocate(c,S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..i-1 : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched,i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* Client c returns a set of resources that it holds. It may do so     *)
(* even before its full request has been honored.                      *)
Return(c,S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat,sched>>

(* The allocator extends its schedule by adding the processes from     *)
(* the set of clients to be scheduled, in some unspecified order.      *)
Schedule == 
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \circ sq
  /\ UNCHANGED <<unsat,alloc>>

(* The next-state relation per client and set of resources.            *)
Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c,S) \/ Allocate(c,S) \/ Return(c,S)
  \/ Schedule

vars == <<unsat,alloc,sched>>

-------------------------------------------------------------------------

(***********************************************************************)
(* Liveness assumptions:                                               *)
(* - Clients must return resources if their request has been satisfied.*)
(* - The allocator must eventually allocate resources when possible.   *)
(* - The allocator must schedule the processes in the pool.            *)
(***********************************************************************)

Liveness ==
  /\ \A c \in Clients : WF_vars(unsat[c]={} /\ Return(c,alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)

(* The specification of the scheduling allocator. *)
Allocator == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------

ResourceMutex ==   \** resources are allocated exclusively
  \A c1,c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

UnscheduledClients ==    \** clients that do not appear in the schedule
  Clients \ Range(sched)

PrevResources(i) ==
  \** resources that will be available when client i has to be satisfied
  available
  \cup (UNION {unsat[sched[j]] \cup alloc[sched[j]] : j \in 1..i-1})
  \cup (UNION {alloc[c] : c \in UnscheduledClients})

AllocatorInvariant ==  \** a lower-level invariant
  /\ \** all clients in the schedule have outstanding requests
     \A i \in DOMAIN sched : unsat[sched[i]] # {}
  /\ \** all clients that need to be scheduled have outstanding requests
     \A c \in toSchedule : unsat[c] # {}
  /\ \** clients never hold a resource requested by a process earlier
     \** in the schedule
     \A i \in DOMAIN sched : \A j \in 1..i-1 : 
        alloc[sched[i]] \cap unsat[sched[j]] = {}
  /\ \** the allocator can satisfy the requests of any scheduled client
     \** assuming that the clients scheduled earlier release their resources
     \A i \in DOMAIN sched : unsat[sched[i]] \subseteq PrevResources(i)

ClientsWillReturn ==
  \A c \in Clients: (unsat[c]={} ~> alloc[c]={})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : r \in unsat[c] ~> r \in alloc[c]

InfOftenSatisfied == 
  \A c \in Clients : []<>(unsat[c] = {})

(* Used for symmetry reduction with TLC.
   Note: because of the schedule sequence, the specification is no
   longer symmetric with respect to the processes!
*)
Symmetry == Permutations(Resources)

-------------------------------------------------------------------------

THEOREM Allocator => []TypeInvariant
THEOREM Allocator => []ResourceMutex
THEOREM Allocator => []AllocatorInvariant
THEOREM Allocator => ClientsWillReturn
THEOREM Allocator => ClientsWillObtain
THEOREM Allocator => InfOftenSatisfied

=========================================================================
