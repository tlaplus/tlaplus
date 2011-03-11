------------------------------ MODULE Promises ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(*                          Objects, Heaps, and Methods                    *)
(***************************************************************************)
CONSTANT Id, Value, Type
  (*************************************************************************)
  (* A value represents something like an int or a boolean.  An Id is the  *)
  (* heap address of an object.  We can represent `null' as some           *)
  (* particular Id.  We assume that an Id is not a Value.  A Type is the   *)
  (* name of a class of objects.                                           *)
  (*************************************************************************)
ASSUME Id \cap Value = {}

(***************************************************************************)
(*                         Some TLA+ Notation                              *)
(*                                                                         *)
(* A function f has a domain written DOMAIN f .  The function assigns a    *)
(* value f[x] for every element x in DOMAIN f.  The domain of a function   *)
(* can be an infinite set.                                                 *)
(*                                                                         *)
(* [S -> T] is the set of all functions f with domain S such that f[x] is  *)
(* in the set T for all x in S.                                            *)
(*                                                                         *)
(* A record r is a function whose domain is a non-empty finite set of      *)
(* strings, where we can write r.fldName as an abbreviation for            *)
(* r["fldName"].                                                           *)
(*                                                                         *)
(* [foo |-> 42, bar |-> v] is the record r whose domain is {"foo", "bar"}  *)
(* such that r.foo = 42 and r.bar = v.                                     *)
(*                                                                         *)
(* [foo : Nat, bar : V] is the set of all records [foo |-> n, bar |-> v]   *)
(* such that n is in Nat and v is in V.                                    *)
(***************************************************************************)
R && S == 
  (*************************************************************************)
  (* If R and S are sets of records, then this defines R && S to be the    *)
  (* set of all records obtained by "concatenating" a record from R and a  *)
  (* record from S, where the concatenating two records means combining    *)
  (* the fields from both.                                                 *)
  (*************************************************************************)
  LET Concat(r, s) == [x \in (DOMAIN r) \cup (DOMAIN s) |-> 
                         IF x \in DOMAIN r THEN r[x] ELSE s[x]]
  IN  {Concat(r, s) : r \in R, s \in S}

CONSTANT Field
  (*************************************************************************)
  (* A Field is a possible name of a field.  We could let Field be the set *)
  (* STRING of all strings.  However, because STRING is a built-in TLA+    *)
  (* primitive, TLC does not allow us to substitute some other set for it  *)
  (* for testing.  Therefore, it's more convenient to let it be an         *)
  (* arbitrary set of strings.  We assume it contains the element "type".  *)
  (*************************************************************************)
ASSUME  /\ Field \subseteq STRING
        /\ "type" \in Field
        
Object == 
  (*************************************************************************)
  (* An Object is a record containing a `type' field that is a Type, whose *)
  (* fields are either Values, Ids, or sequences of Values and/or Ids.     *)
  (* (We won't need of sequences of sequences of...) The fields of the     *)
  (* record represent the non-static fields of the object.  If we wanted   *)
  (* to model classes and static fields, we would make a class an object   *)
  (* whose fields are the class's static fields, and let each object have  *)
  (* a field that contains the Id of the class.                            *)
  (*************************************************************************)
  LET Rcd(Labels) == 
       { R \in [Labels -> Value \cup Id \cup Seq(Value \cup Id) \cup Type] : 
           /\ R.type \in Type
           /\ \A x \in Labels \ {"type"} : 
                  R[x] \in Value \cup Id \cup Seq(Value \cup Id)}
      LabelSets == { S \in SUBSET Field : IsFiniteSet(S) /\ ("type" \in S) }
  IN  UNION {Rcd(Labels) : Labels \in LabelSets}
  
Heap == [Id -> Object \cup {<< >>}]
  (*************************************************************************)
  (* A Heap maps an Dd either to an Object or to << >>, the latter meaning *)
  (* that the Id is not the Id of any object.                              *)
  (*************************************************************************)

ReachableFrom(obj, H) ==
  (*************************************************************************)
  (* This is the set of Ids reachable from an Object obj in the heap H.    *)
  (* If obj is not an Object, it is the empty set.  Otherwise, it consists *)
  (* of all the Ids that are values of fields of obj, together with all    *)
  (* the Ids reachable from objects in heap H with those Ids.  It is       *)
  (* defined in terms of two operators IdsOf and R.                        *)
  (*************************************************************************)
  LET Range(f) == {f[x] : x \in DOMAIN f}
        (*******************************************************************)
        (* If f is a sequence, then this is the set of elements in the     *)
        (* sequence.  If f is a record, then this is the set of all values *)
        (* of fields of f.                                                 *)
        (*******************************************************************)

      IdsOf(o) == 
        (*******************************************************************)
        (* If o is an object, then this is the set composed of every Id    *)
        (* that is either the value of a field of object o, or else is an  *)
        (* element of a sequence that is the value of a field of o.  It is *)
        (* the empty set if o is not an object.                            *)
        (*******************************************************************)
        IF o \in Object
          THEN  LET IdSetOf(x) == IF x \in Value
                                    THEN {} 
                                    ELSE IF x \in Id
                                           THEN {x}
                                           ELSE Range(x) \cap Id 
                IN  UNION {IdSetOf(o[fld]) : fld \in (DOMAIN o) \ {"type"}}
          ELSE {}
          
       R[n \in Nat] == 
         (******************************************************************)
         (* Defines R[n] to be the set of Ids reachable from id by a path  *)
         (* of length at most n in the heap H.                             *)
         (******************************************************************)
         IF n = 0 THEN IdsOf(obj)
                  ELSE R[n-1] \cup { IdsOf(H[i]) : i \in R[n-1] }
  IN   UNION {R[n] : n \in Nat}
-----------------------------------------------------------------------------
CONSTANT Exception
  (*************************************************************************)
  (* An Exception is the "value" produced by breaking a promise.           *)
  (*************************************************************************)

ASSUME Exception \cap Value = {}

NotAValue == CHOOSE v : v \notin Value \cup Exception

ToDo ==
  [ args : Seq(Id \cup Value),
      (*********************************************************************)
      (* The arguments of the code.                                        *)
      (*********************************************************************)
    val : Value \cup Exception \cup {NotAValue},
      (*********************************************************************)
      (* When the ToDo is ready to be executed, val is a Value or an       *)
      (* Exception; otherwise it equals NotAValue.                         *)
      (*********************************************************************)
    out : Seq(Id),
      (*********************************************************************)
      (* A sequence of pointers to Eventual objects: ones whose promises   *)
      (* will be resolved (fulfilled or broken) or forwarded when this     *)
      (* ToDo is executed.                                                 *)
      (*********************************************************************)
    successCode : [ Value \X Seq(Id \cup Value) \X Heap ->
                     Seq(Id \cup Value \cup Exception) \X Heap ],
      (*********************************************************************)
      (* The successCode maps the Value val, the sequence args, and a      *)
      (* current heap to a sequence of outputs, one output for every       *)
      (* Eventual object pointed to by the elements of out, and a new      *)
      (* heap.                                                             *)
      (*********************************************************************)
    brokenCode : [ Exception \X Seq(Id \cup Value) \X Heap ->
                     Seq(Id \cup Value \cup Exception) \X Heap ],
      (*********************************************************************)
      (* Like successCode, except for the case val is an Exception.        *)
      (*********************************************************************)
    canMarshall : BOOLEAN
      (*********************************************************************)
      (* Equals TRUE iff the ToDo can be executed in a Vat other than the  *)
      (* one in which it originated.                                       *)
      (*********************************************************************)
  ]

CONSTANT EventualType
ASSUME EventualType \in Type

Eventual ==
  (*************************************************************************)
  (* An Eventual is an object that represents a promise and a resolver for *)
  (* that promise.  (In language terms, it is a class of objects that have *)
  (* a Promise and a Resolver interface.)                                  *)
  (*************************************************************************)
  [ type : {EventualType},
      (*********************************************************************)
      (* An Eventual is an object of type "Eventual".                      *)
      (*********************************************************************)
    todos : Seq(ToDo)
      (*********************************************************************)
      (* The sequence of ToDos to be executed when the promise is          *)
      (* resolved.  Note that even if the promise has been resolved or     *)
      (* forwarded, the todos field may not be an empty sequence because   *)
      (* all the ToDos to be executed upon resolution may not yet have     *)
      (* been forwarded to where they will be executed.                    *)
      (*********************************************************************)
  ]
  
  &&
  
  ( [ a : TRUE
    ]
  )
========================================================================
(***************************************************************************)
(*                               Promises                                  *)
(***************************************************************************)
ResolvedPromise == 
  [ type     : {"promise"},
    resolved : {TRUE},
    value    : Value \cup Id
  ]
                    
UnresolvedPromise ==
  (*************************************************************************)
  (* A promise is resolved by executing a method to compute its value.     *)
  (* There are two kinds of promises: `when' promises and the other kind.  *)
  (* A `when' promise is returned by executing a whenFulfilled such as     *)
  (*                                                                       *)
  (*    foo.whenFulfilled(arg => some code)                                *)
  (*                                                                       *)
  (* The promise is specified by an object with these fields:              *)
  (*                                                                       *)
  (*   - A single-argument Method, which is dynamically created by         *)
  (*     executing the whenFulfilled.  In the example, it is the Method    *)
  (*     that would be written in the class containing the expression as   *)
  (*                                                                       *)
  (*        newMethod(arg) { some code }                                   *)
  (*                                                                       *)
  (*   - The Id of the object for which the whenFulfilled method was       *)
  (*     executed.  In the example, references to `this' in `some code'    *)
  (*     refer to the fields of this object.                               *)
  (*                                                                       *)
  (*   - A promise for method's the single argument.  In the example,      *)
  (*     it is a promise for foo.                                          *)
  (*                                                                       *)
  (* A non-`when' promise is one produced by executing something like      *)
  (*                                                                       *)
  (*   foo.Bar(arg1, ... , argN)                                           *)
  (*                                                                       *)
  (* The promise is specified by an object with these fields:              *)
  (*                                                                       *)
  (*   - A Method that represents the Bar method of the appropriate        *)
  (*     class.                                                            *)
  (*                                                                       *)
  (*   - A promise for an Id of the object foo.                            *)
  (*                                                                       *)
  (*   - The argument list.                                                *)
  (*                                                                       *)
  (* Because a promise is an Object, promises can appear just like any     *)
  (* other object in the heap.  They can also be used as arguments to      *)
  (* methods.                                                              *)
  (*************************************************************************)
  [ type       : {"promise"},
    resolved   : {FALSE},
    method     : Method,
    isWhen     : {TRUE},
    objId      : Id,
    argPromise : Id
  ]
  
  \cup
  
  [ type         : {"promise"},
    resolved     : {FALSE},
    method       : Method,
    isWhen       : {FALSE},
    objIdPromise : Id,
    args         : Seq(Value \cup Id)
  ]

Promise == ResolvedPromise \cup UnresolvedPromise

OKObject == {o \in Object : o.type = "promise" => o \in Promise} 
  (*************************************************************************)
  (* The set Object minus those objects of type "promise" that are not in  *)
  (* the set Promise.                                                      *)
  (*************************************************************************)

OKHeap ==
  (*************************************************************************)
  (* The set of Heaps such that:                                           *)
  (*                                                                       *)
  (*   - There are  no dangling pointers (fields of objects                *)
  (*     that are Ids that point to nothing).                              *)
  (*                                                                       *)
  (*   - Every Id in that should be the Id of a promise is.                *)
  (*                                                                       *)
  (*   - There are no cycles of promises                                   *)
  (*************************************************************************)
  {H \in Heap : 
    \A id \in Id : 
       LET obj == H[id]
       IN  (obj # << >>) =>
              /\ obj \in OKObject
              /\ \A fldName \in DOMAIN obj :
                    (obj[fldName] \in Id) => (H[obj[fldName]] # << >>)
              /\ (obj \in Promise) /\ (~ obj.resolved) =>
                    /\ IF obj.isWhen THEN H[obj.argPromise] \in Promise
                                     ELSE H[obj.objIdPromise] \in Promise  
                    /\ LET thePromise(i) == 
                             IF H[i].resolved 
                               THEN i
                               ELSE IF H[i].isWhen THEN H[i].argPromise
                                                   ELSE H[i].objIdPromise
                           R[n \in Nat] ==
                              IF n = 0 THEN id
                                       ELSE thePromise(R[n-1])
                       IN  \A n \in Nat \ {0} : R[n] # id                  } 
       
ReachableWithoutPromises(obj, H) == 
  (*************************************************************************)
  (* Like ReachableFrom, except that it does not follow links inside       *)
  (* objects of type "promise", which as described above represent         *)
  (* promises.                                                             *)
  (*************************************************************************)
  LET IdsOf(o) == 
        (*******************************************************************)
        (* The set of all values of fields of object obj that are Ids, or  *)
        (* the empty set if obj is not an object.                          *)
        (*******************************************************************)
        IF (o \in Object) /\ (o.type # "promise")
          THEN {i \in {o[x] : x \in DOMAIN o} : i \in Id}
          ELSE {}          
       R[n \in Nat] == 
         (******************************************************************)
         (* Defines R[n] to be the set of Ids reachable from id by a path  *)
         (* of length at most n in the heap H.                             *)
         (******************************************************************)
         IF n = 0 THEN IdsOf(obj)
                  ELSE R[n-1] \cup { IdsOf(H[i]) : i \in R[n-1] }
  IN   UNION {R[n] : n \in Nat}


ASSUME \A M \in Method, 
          obj \in OKObject,
          args \in Seq(Value \cup Id) : 
         LET E(H) == Eval(M, obj, args, H)
             UseableId(H) == ReachableWithoutPromises(obj, H) \cup 
                               UNION {ReachableWithoutPromises(args[i], H) : 
                                        i \in 1..Len(args)}
         IN  /\ \A H \in OKHeap : 
                  /\ E(H) \in [result : Value \cup Id, heap : OKHeap]
                     (******************************************************)
                     (* For convenience, we assume that evaluating method  *)
                     (* M produces some result and new heap for arbitrary  *)
                     (* OKObject obj, argument list args, and heap H even  *)
                     (* when they are meaningless--for example, if the     *)
                     (* result of executing M depends on the values of     *)
                     (* fields of obj that do not exist.                   *)
                     (******************************************************)
                  /\ \A id \in Id :
                        (H[id] # E(H).heap[id]) => \/ id \in UseableId(H)
                                                   \/ H[id] = << >>
                     (******************************************************)
                     (* Evaluating M can modify the heap only by modifying *)
                     (* objects whose Id is reachable from obj or an       *)
                     (* argument and by creating new objects.              *)
                     (******************************************************)
             /\ \A H1, H2 \in OKHeap : 
                  /\ UseableId(H1) = UseableId(H2)
                  /\ \A id \in UseableId(H1) : H1[id] = H2[id]
                  =>  /\ E(H1).result = E(H2).result
                      /\ \A id \in Id : (H1[id] # E(H1).heap[id]) =>
                                          (E(H1).heap[id] = E(H2).heap[id])
                 (**********************************************************)
                 (* If two heaps are the same on the Ids reachable from    *)
                 (* obj and the arguments, then evaluating M in the two    *)
                 (* heaps produces the same result, and it produces the    *)
                 (* same changes to the two heaps.                         *)
                 (**********************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                               Actions                                   *)
(***************************************************************************)
VARIABLE heap  \* The variable whose value is the current Heap.

ResolveWhenPromise(id) ==
  (*************************************************************************)
  (* The action that modifies the heap by resolving a `when' promise when  *)
  (* the promise it is waiting for has been resolved.                      *)
  (*************************************************************************)
   LET promise == heap[id]
   IN  /\ promise \in Promise
       /\ ~ promise.resolved 
       /\ promise.isWhen
       /\ heap[promise.argPromise].resolved
       /\ heap' =
           LET E == Eval(promise.method, 
                         heap[promise.objId], 
                         <<heap[promise.argPromise].value>>,
                         heap)
           IN  [E.heap EXCEPT ![id] = [type     |-> "promise",
                                       resolved |-> TRUE,
                                       value    |-> E.result]]
              
ResolveNonWhenPromise(id) ==
  (*************************************************************************)
  (* The action that modifies the heap by resolving a non-`when' promise   *)
  (* when the promise it is waiting for has been resolved.                 *)
  (*************************************************************************)
   LET promise == heap[id]
   IN  /\ promise \in Promise
       /\ ~ promise.resolved 
       /\ ~promise.isWhen
       /\ heap[promise.objIdPromise].resolved
       /\ heap' =
           LET E == Eval(promise.method, 
                         heap[heap[promise.objIdPromise].value], 
                         promise.args,
                         heap)
           IN  [E.heap EXCEPT ![id] = [type     |-> "promise",
                                       resolved |-> TRUE,
                                       value    |-> E.result]]

GarbageCollectResolvedPromise(id) ==
  (*************************************************************************)
  (* The action that garbage collects a promise that has been resolved and *)
  (* whose value is no longer usable.                                      *)
  (*************************************************************************)
  /\ heap[id] \in Promise
  /\ heap[id].resolved
  /\ \A i \in Id \ {id} :
        (heap[i] # << >>) => \A fldName \in DOMAIN i : 
                                (heap[i][fldName] \in Id) => 
                                  (heap[heap[i][fldName]] # id)
  /\ heap' = [heap EXCEPT ![id] = << >>]
  

=============================================================================
\* Modification History
\* Last modified Thu Mar 10 15:56:13 PST 2011 by lamport
\* Created Sat Mar 05 13:24:42 PST 2011 by lamport
