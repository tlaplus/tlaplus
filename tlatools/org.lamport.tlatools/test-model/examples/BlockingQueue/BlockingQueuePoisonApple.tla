---------------------- MODULE BlockingQueuePoisonApple ----------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC, TLCExt

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity, (* the maximum number of messages in the bounded buffer  *)
          Poison

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)
       
-----------------------------------------------------------------------------

\* prod maps each producer to its apple slices that it will eventually send to
\* consumers. cons maps each consumer to the apple slices it has eaten so far. 
VARIABLES prod, cons

-----------------------------------------------------------------------------

ap ==
    \* The set of active producers, i.e., producers that have yet to send out
    \* some bites of their poison apple.
    {p \in DOMAIN prod: prod[p] > 0} \* <=> prod \notin [P -> {0}]

ac == 
    \* The set of active consumers, i.e., consumers that have yet to take a
    \* bite of poison apples before they die/can terminate.
    {c \in DOMAIN cons: cons[c] > 0} \* <=> cons \notin [C -> {0}]

-----------------------------------------------------------------------------

VARIABLES buffer, waitSet
vars == <<buffer, waitSet, prod, cons>>

NotifyOther(Others) == 
    IF waitSet \cap Others # {}
    THEN \E t \in waitSet \cap Others : waitSet' = waitSet \ {t}
    ELSE UNCHANGED waitSet

(* @see java.lang.Object#wait *)
Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>

-----------------------------------------------------------------------------

(* 
  Contrary to PoisonPill, there is no dedicated "janitor" process that requires
  some form of *external* synchronization. Global termination is achieved without
  synchronizing producers.  Instead, the tradeoff of this variant is a tighter
  coupling between producers and consumers because producers *and* consumers
  need to know the number (cardinality) of the other role (see the definition of
  prod  and cons  in  Init  below to see why that is).
  Why is this complexity necessary, why can't we just have each producer send
  a poison pill to one consumer (and some producers send more than one pill iff
  |C| > |P|)? While this would work iff |C| >= |P|, it fails if |C| < |P|. Let
  P_p be the subset of P such that |P_p| = |C|, i.e. the producers that poison
  consumers. If one or more of the producers not in P_p remain active after all
  producers in P_p terminated, there are no (active) consumers left.
*)
Put(t, d) ==
    /\ t \notin waitSet
    \* The Producer t must not have initiated its termination.
    /\ prod[t] > 0
    /\ \/ /\ Len(buffer) < BufCapacity
          /\ \/ /\ buffer' = Append(buffer, d)
                /\ UNCHANGED prod
             \/ /\ buffer' = Append(buffer, Poison)
                \* Producer t messages one consumer.
                /\ prod' = [ prod EXCEPT ![t] = @ - 1]
          /\ NotifyOther(Consumers)
       \/ /\ Len(buffer) = BufCapacity
          /\ Wait(t)
          /\ UNCHANGED prod
    /\ UNCHANGED <<cons>>
   
Get(t) ==
/\ t \notin waitSet
/\ cons[t] > 0
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(Producers)
      /\ \/ /\ Head(buffer) # Poison
            /\ UNCHANGED <<prod,cons>>
         \/ /\ Head(buffer) = Poison
            /\ cons' = [ cons EXCEPT ![t] = @ - 1]
            /\ UNCHANGED <<prod>>
   \/ /\ buffer = <<>>
      /\ Wait(t)
      /\ UNCHANGED <<prod,cons>>

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == 
    /\ buffer = <<>>
    /\ waitSet = {}
    \* The system requires |C| * |P| poison pills to terminate reliably. Perhaps,
    \* this is what Goetz et. al. mean by "unwiedly" on page 156 in their book
    \* Java Concurrency in Practice. However, it is unclear why the authors write
    \* on the same page that "Poison pills work reliably only with unbounded queues."
    /\ cons = [ c \in Consumers |-> Cardinality(Producers) ]
    /\ prod = [ p \in Producers |-> Cardinality(Consumers) ]

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == 
    \/ \E p \in Producers: Put(p, p) \* Add some data to buffer
    \/ \E c \in Consumers: Get(c)

Spec ==
    /\ Init 
    /\ [][Next]_vars
    /\ \A c \in Consumers : WF_vars(Get(c)) 
    /\ \A p \in Producers : WF_vars(Put(p, p))

-----------------------------------------------------------------------------

(* TLA+ is untyped, thus lets verify the range of some values in each state. *)
TypeInv == 
    /\ buffer \in Seq(Producers \cup {Poison})
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitSet \in SUBSET (Producers \cup Consumers)
    /\ prod \in [ Producers -> 0..Cardinality(Consumers) ]
    /\ cons \in [ Consumers -> 0..Cardinality(Producers) ]

(* No Deadlock *)
NoDeadlock == waitSet # (Producers \cup Consumers)

THEOREM Spec => [](TypeInv /\ NoDeadlock)
-----------------------------------------------------------------------------

\* The queue is empty after (global) termination.
QueueEmpty ==
    []((ap \cup ac) = {}) => (buffer = <<>>)

\* The system terminates iff all producers terminate.
GlobalTermination ==
    (ap = {}) ~> [](ac = {})

THEOREM Spec => QueueEmpty /\ GlobalTermination
-----------------------------------------------------------------------------

SSpec ==
    /\ Init 
    /\ [][Next]_vars
    /\ \A c \in Consumers : WF_vars(Get(c))
    \* This fairness constraint causes all producers to eventually terminate.
    /\ \A p \in Producers : SF_vars(Put(p, p) /\ prod' # prod)

Terminates ==
    <>[](ap = {})

THEOREM SSpec => Terminates

BufferInfOftenNonEmpty == \A p \in Producers: []<><<Put(p, p)>>_vars

CONSTANT p1, p2, c1, c2
PostCondition ==
   CounterExample =
   [ action |->
      { << << 1,
              [ prod |-> (p1 :> 2 @@ p2 :> 2),
                cons |-> (c1 :> 2 @@ c2 :> 2),
                buffer |-> <<>>,
                waitSet |-> {} ] >>,
           [ name |-> "Put",
             location |->
                 [ beginLine |-> 64,
                   beginColumn |-> 5,
                   endLine |-> 77,
                   endColumn |-> 25,
                   module |-> "BlockingQueuePoisonApple" ],
             context |-> [t |-> p2, d |-> p2],
             parameters |-> <<"t", "d">> ],
           << 2,
              [ prod |-> (p1 :> 2 @@ p2 :> 1),
                cons |-> (c1 :> 2 @@ c2 :> 2),
                buffer |-> <<Poison>>,
                waitSet |-> {} ] >> >>,
        << << 2,
              [ prod |-> (p1 :> 2 @@ p2 :> 1),
                cons |-> (c1 :> 2 @@ c2 :> 2),
                buffer |-> <<Poison>>,
                waitSet |-> {} ] >>,
           [ name |-> "Get",
             location |->
                 [ beginLine |-> 80,
                   beginColumn |-> 1,
                   endLine |-> 92,
                   endColumn |-> 32,
                   module |-> "BlockingQueuePoisonApple" ],
             context |-> [t |-> c2],
             parameters |-> <<"t">> ],
           << 3,
              [ prod |-> (p1 :> 2 @@ p2 :> 1),
                cons |-> (c1 :> 2 @@ c2 :> 1),
                buffer |-> <<>>,
                waitSet |-> {} ] >> >>,
        << << 3,
              [ prod |-> (p1 :> 2 @@ p2 :> 1),
                cons |-> (c1 :> 2 @@ c2 :> 1),
                buffer |-> <<>>,
                waitSet |-> {} ] >>,
           [ name |-> "Put",
             location |->
                 [ beginLine |-> 64,
                   beginColumn |-> 5,
                   endLine |-> 77,
                   endColumn |-> 25,
                   module |-> "BlockingQueuePoisonApple" ],
             context |-> [t |-> p2, d |-> p2],
             parameters |-> <<"t", "d">> ],
           << 4,
              [ prod |-> (p1 :> 2 @@ p2 :> 0),
                cons |-> (c1 :> 2 @@ c2 :> 1),
                buffer |-> <<Poison>>,
                waitSet |-> {} ] >> >>,
        << << 4,
              [ prod |-> (p1 :> 2 @@ p2 :> 0),
                cons |-> (c1 :> 2 @@ c2 :> 1),
                buffer |-> <<Poison>>,
                waitSet |-> {} ] >>,
           [ name |-> "Get",
             location |->
                 [ beginLine |-> 80,
                   beginColumn |-> 1,
                   endLine |-> 92,
                   endColumn |-> 32,
                   module |-> "BlockingQueuePoisonApple" ],
             context |-> [t |-> c1],
             parameters |-> <<"t">> ],
           << 5,
              [ prod |-> (p1 :> 2 @@ p2 :> 0),
                cons |-> (c1 :> 1 @@ c2 :> 1),
                buffer |-> <<>>,
                waitSet |-> {} ] >> >>,
        << << 5,
              [ prod |-> (p1 :> 2 @@ p2 :> 0),
                cons |-> (c1 :> 1 @@ c2 :> 1),
                buffer |-> <<>>,
                waitSet |-> {} ] >>,
           [ name |-> "Put",
             location |->
                 [ beginLine |-> 64,
                   beginColumn |-> 5,
                   endLine |-> 77,
                   endColumn |-> 25,
                   module |-> "BlockingQueuePoisonApple" ],
             context |-> [t |-> p1, d |-> p1],
             parameters |-> <<"t", "d">> ],
           << 6,
              [ prod |-> (p1 :> 1 @@ p2 :> 0),
                cons |-> (c1 :> 1 @@ c2 :> 1),
                buffer |-> <<Poison>>,
                waitSet |-> {} ] >> >>,
        << << 6,
              [ prod |-> (p1 :> 1 @@ p2 :> 0),
                cons |-> (c1 :> 1 @@ c2 :> 1),
                buffer |-> <<Poison>>,
                waitSet |-> {} ] >>,
           [ name |-> "Put",
             location |->
                 [ beginLine |-> 64,
                   beginColumn |-> 5,
                   endLine |-> 77,
                   endColumn |-> 25,
                   module |-> "BlockingQueuePoisonApple" ],
             context |-> [t |-> p1, d |-> p1],
             parameters |-> <<"t", "d">> ],
           << 7,
              [ prod |-> (p1 :> 0 @@ p2 :> 0),
                cons |-> (c1 :> 1 @@ c2 :> 1),
                buffer |-> <<Poison, Poison>>,
                waitSet |-> {} ] >> >>,
        << << 7,
              [ prod |-> (p1 :> 0 @@ p2 :> 0),
                cons |-> (c1 :> 1 @@ c2 :> 1),
                buffer |-> <<Poison, Poison>>,
                waitSet |-> {} ] >>,
           [ name |-> "Get",
             location |->
                 [ beginLine |-> 80,
                   beginColumn |-> 1,
                   endLine |-> 92,
                   endColumn |-> 32,
                   module |-> "BlockingQueuePoisonApple" ],
             context |-> [t |-> c2],
             parameters |-> <<"t">> ],
           << 8,
              [ prod |-> (p1 :> 0 @@ p2 :> 0),
                cons |-> (c1 :> 1 @@ c2 :> 0),
                buffer |-> <<Poison>>,
                waitSet |-> {} ] >> >>,
        << << 8,
              [ prod |-> (p1 :> 0 @@ p2 :> 0),
                cons |-> (c1 :> 1 @@ c2 :> 0),
                buffer |-> <<Poison>>,
                waitSet |-> {} ] >>,
           [ name |-> "Get",
             location |->
                 [ beginLine |-> 80,
                   beginColumn |-> 1,
                   endLine |-> 92,
                   endColumn |-> 32,
                   module |-> "BlockingQueuePoisonApple" ],
             context |-> [t |-> c1],
             parameters |-> <<"t">> ],
           << 9,
              [ prod |-> (p1 :> 0 @@ p2 :> 0),
                cons |-> (c1 :> 0 @@ c2 :> 0),
                buffer |-> <<>>,
                waitSet |-> {} ] >> >>,
        << << 9,
              [ prod |-> (p1 :> 0 @@ p2 :> 0),
                cons |-> (c1 :> 0 @@ c2 :> 0),
                buffer |-> <<>>,
                waitSet |-> {} ] >>,
           [ name |-> "Get",
             location |->
                 [ beginLine |-> 80,
                   beginColumn |-> 1,
                   endLine |-> 92,
                   endColumn |-> 32,
                   module |-> "BlockingQueuePoisonApple" ],
             context |-> [t |-> c1],
             parameters |-> <<"t">> ],
           << 9,
              [ prod |-> (p1 :> 0 @@ p2 :> 0),
                cons |-> (c1 :> 0 @@ c2 :> 0),
                buffer |-> <<>>,
                waitSet |-> {} ] >> >> },
  state |->
      { << 1,
           [ prod |-> (p1 :> 2 @@ p2 :> 2),
             cons |-> (c1 :> 2 @@ c2 :> 2),
             buffer |-> <<>>,
             waitSet |-> {} ] >>,
        << 2,
           [ prod |-> (p1 :> 2 @@ p2 :> 1),
             cons |-> (c1 :> 2 @@ c2 :> 2),
             buffer |-> <<Poison>>,
             waitSet |-> {} ] >>,
        << 3,
           [ prod |-> (p1 :> 2 @@ p2 :> 1),
             cons |-> (c1 :> 2 @@ c2 :> 1),
             buffer |-> <<>>,
             waitSet |-> {} ] >>,
        << 4,
           [ prod |-> (p1 :> 2 @@ p2 :> 0),
             cons |-> (c1 :> 2 @@ c2 :> 1),
             buffer |-> <<Poison>>,
             waitSet |-> {} ] >>,
        << 5,
           [ prod |-> (p1 :> 2 @@ p2 :> 0),
             cons |-> (c1 :> 1 @@ c2 :> 1),
             buffer |-> <<>>,
             waitSet |-> {} ] >>,
        << 6,
           [ prod |-> (p1 :> 1 @@ p2 :> 0),
             cons |-> (c1 :> 1 @@ c2 :> 1),
             buffer |-> <<Poison>>,
             waitSet |-> {} ] >>,
        << 7,
           [ prod |-> (p1 :> 0 @@ p2 :> 0),
             cons |-> (c1 :> 1 @@ c2 :> 1),
             buffer |-> <<Poison, Poison>>,
             waitSet |-> {} ] >>,
        << 8,
           [ prod |-> (p1 :> 0 @@ p2 :> 0),
             cons |-> (c1 :> 1 @@ c2 :> 0),
             buffer |-> <<Poison>>,
             waitSet |-> {} ] >>,
        << 9,
           [ prod |-> (p1 :> 0 @@ p2 :> 0),
             cons |-> (c1 :> 0 @@ c2 :> 0),
             buffer |-> <<>>,
             waitSet |-> {} ] >> } ]

=============================================================================
