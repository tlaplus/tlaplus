--------------------------- MODULE test27 ----------------------------------
(***************************************************************************)
(* A fingerprint test that models LazyCache.                               *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Addr,         (* A set                         *)
         Data,         (* A set                         *)
         InitData,     (* A subset of Data              *)
         ND,           (* A model value                 *)
         N,            (* The number of processors      *)
         InLen, OutLen (* Maximum lengths of in and out *)

VARIABLE mem, c, in, out

Proc == 1..N


Exp(a, m) ==
  (*************************************************************************)
  (* Recursive definition of a^n.                                          *)
  (*************************************************************************)
  LET E[n \in Nat] == IF n = 0 THEN 1 ELSE a * E[n-1]
  IN  E[m]

CountSeq(S, len) ==
  (*************************************************************************)
  (* Number of elements in Seq(S) of length \leq len.                      *)
  (*************************************************************************)
  LET CS[n \in Nat] == 
        (*******************************************************************)
        (* Recursive definition of CountSeq(S, n).  There are              *)
        (* (Cardinality(S))^n sequences of length n.                       *)
        (*******************************************************************)
         IF n = 0 THEN 1
                  ELSE Exp(Cardinality(S), n) + CS[n-1]       
  IN  CS[len]


Op  ==  (Data \X Addr) \cup {<<d, a, "*">> : d \in Data, a \in Addr}
                            (***********************************************)
                            (* Have to write Data \X Addr \X {"*"}         *)
                            (* in this way.                                *)
                            (***********************************************)
                            
Restrict(f) == 
    { g \in  [Addr -> Data \cup  { ND  }] :
                   \A  a \in  Addr: g[a] \in  { f[a] , ND  } } 

Init == /\ Print(LET D == Cardinality(Data)
                     A == Cardinality(Addr)
                     P == Cardinality(Proc)
                 IN <<"Number of distinct states =", 
                        Exp(D, A)                    (* No. of values of mem *)
                      * Exp(D+1, P * A)              (* No. of values of c   *)
                      * Exp(CountSeq(Op, InLen), P)  (* No. of values of in  *)
                      * Exp(CountSeq(Data \X Addr, OutLen), P) (* No. of values of out *)
                    >>, TRUE)
        /\ mem \in  [Addr -> InitData] 
        /\ c \in  [Proc -> Restrict(mem)] 
        /\ in  = [i \in  Proc |-> <<>>]    
        /\ out = [i \in  Proc |-> <<>>]                  

Inv ==
  /\ IF mem \in [Addr -> Data] 
       THEN TRUE
       ELSE /\ Print("Conj 1 False", TRUE)
            /\ FALSE
  /\ IF c   \in [Proc -> [Addr -> (Data \cup {ND})] ] 
       THEN TRUE
       ELSE /\ Print("Conj 2 False", TRUE)
            /\ FALSE
  /\ IF in  \in [Proc -> Seq(Op)]
       THEN TRUE
       ELSE /\ Print("Conj 3 False", TRUE)
            /\ FALSE
  /\ IF \A p \in Proc: Len(in[p]) \leq InLen
       THEN TRUE
       ELSE /\ Print("Conj 4 False", TRUE)
            /\ FALSE
  /\ IF out \in [Proc -> Seq(Data \X Addr)] 
       THEN TRUE
       ELSE /\ Print("Conj 5 False", TRUE)
            /\ FALSE
  /\ IF \A p \in Proc: Len(out[p]) \leq OutLen
       THEN TRUE
       ELSE /\ Print("Conj 6 False", TRUE)
            /\ FALSE

Next ==
  \/ UNCHANGED <<mem, c, in, out>>

  \/ /\ \E a \in Addr, d \in Data : mem' = [mem EXCEPT ![a] = d]
     /\ UNCHANGED <<c, in, out>>

  \/ \E p \in Proc : 

        \/ /\ \E a \in Addr,  d \in Data \cup {ND} :
                  c' = [c EXCEPT ![p][a] = d]
           /\ UNCHANGED <<mem,  in, out>>

        \/ /\ Len(out[p]) < OutLen
           /\ \E o \in Data \X Addr : out' = [out EXCEPT ![p] = @ \o <<o>>]
           /\ UNCHANGED <<mem, c, in>>

        \/ /\ Len(in[p]) < InLen
           /\ \E o \in Op : in' = [in EXCEPT ![p] = @ \o <<o>>]
           /\ UNCHANGED <<mem, c, out>>

        \/ /\ out[p] # << >> 
           /\ out' = [out EXCEPT ![p] = Tail(@)]
           /\ UNCHANGED <<mem, c, in>>

        \/ /\ in[p] # << >> 
           /\ in' = [in EXCEPT ![p] = Tail(@)]
           /\ UNCHANGED <<mem, c, out>>



=============================================================================
