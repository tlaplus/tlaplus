------------------------- MODULE NQSpecImpliesQSpec -------------------------
EXTENDS NQSpec, FiniteSets, TLC

\*NoData == NotData
NatSetMax(S) == IF S = {} THEN 0 ELSE CHOOSE n \in S : \A m \in S : n >=m
VARIABLE p, \* The prophecy variable = sequence of next values read,
            \* of length Cardinality(elts)
         Q, \* The queue of QSpec, except as Elements with their Ids,
            \* and except that it is changed only on the actions
            \* of NQSpec.  Added as a history variable.
         s,
            \* A stuttering variable to add the actions
            \* corresponding to the DoEnq and DoDeq actions of QSpec
         enqInner, deqInner
            \* History variables implementing the corresponding variables
            \* of  QSpec, except deqInner gets set to an Element el instead
            \* of el.data

\* The order of adding the variables is:
\*   s, p, Q, {queue, enqInner, deqInner}
varsI == <<vars, p, Q,  s, enqInner, deqInner>>

top == CHOOSE t : t \notin {}
bot == [EndEnq |-> TRUE, EndDeq |-> TRUE]

TypeOKI == /\ TypeOK
           /\ Q \in Seq(Elements)
           /\ p \in Seq(Elements)
           /\ s \in {top} 
                 \cup [type : {"EndDeq"}, name : DeQers \X Elements, val : {FALSE, TRUE}]
                 \cup [type : {"EndEnq"}, name : EnQers, val : {TRUE}]
                 \cup [type : {"BeginEnq"}, name : EnQers, val : Seq(Elements)] 
           /\ enqInner \in [EnQers -> {Done, Busy}]
           /\ deqInner \in [DeQers -> {NoData} \cup Elements]

InitI == /\ Init
         /\ Q = << >>
         /\ enqInner = [e \in EnQers |-> Done]
         /\ \E i \in Ids : deqInner = [d \in DeQers |-> [data |-> InitData,
                                                         id |-> i]]
         /\ p = << >>
         /\ s = top
         /\ TLCSet(1, {})

RemoveFrom(E, After) == [x \in (DOMAIN After) \  E |-> After[x] \ E]
RECURSIVE IsConsistent(_, _)
IsConsistent(seq, After) ==
  IF seq = << >>
    THEN TRUE
    ELSE LET hd == Head(seq)
             Elts == DOMAIN After
         IN /\ (hd \in DOMAIN After) /\ (After[hd] = {})
            /\ IsConsistent(Tail(seq),
                            RemoveFrom({hd}, After))
                            
IsBlocking(el, After) == LET Elts == DOMAIN After
                             MinElts == MinimalElts(After)
                         IN  (el \notin MinElts) /\ (doneElts # {})


AllEnabled == s = top

PostStutterEnabled(type, name) == (s # top) /\ (s.type = type) /\ (s.name = name)
PreStutterEnabled(type, name) ==  (s # top) =>
                                     /\ (s.type = type) /\ (s.name = name)
                                     /\ s.val # bot[s.type]
AfterPreStutterEnabled(type, name) == /\ s # top
                                      /\ (s.type = type) /\ (s.name = name)
                                      /\ s.val = bot[s.type]
                              
SetStutter(type, name, val) == 
   /\ (s # top) =>  Assert(s.type = type /\ s.name = name,
                           "SetStutter not executed by owner of stuttering variable")
   /\ s' = [type |-> type, name |-> name, val |-> val]
   
Prefix(n, seq) == [i \in 1..n |-> seq[i]]
Suffix(n, seq) == [i \in 1..(Len(seq)-n) |-> seq[i+n]]
SeqElts(seq) == {seq[i] : i \in 1..Len(seq)}

PInv == /\ Cardinality(elts) = Len(p)

QInv == /\ Cardinality(SeqElts(Q)) = Len(Q) 
        /\ SeqElts(Q) \subseteq elts
        /\ IsConsistent(Q, after)
        /\ LET n == NatSetMax({i \in 1..Len(Q) : Prefix(i, Q) = Prefix(i, p)})
           IN (n < Len(Q)) => IsBlocking(p[n+1], 
                                         RemoveFrom(SeqElts(Prefix(n, Q)), after))  

Writer(elt) == CHOOSE e \in EnQers : adding[e] = elt

BeginEnqI(e) == /\ AllEnabled 
                /\ BeginEnq(e) 
                /\ \E el \in Elements : p' = Append(p, el)
\*                /\ TLCSet(1, {p'} \cup TLCGet(1))
\*                /\ IF (Elements \X Elements \subseteq TLCGet(1))
\*                     THEN /\ PrintT(TLCGet(1))
\*                          /\ Assert (FALSE, "There")
\*                     ELSE TRUE
\*\*                /\ PrintT(<<e, p, p', after'>>)
                /\ LET RECURSIVE ToAdd(_, _)
                       ToAdd(i, After) == 
                         IF (i > Len(p')) \/ p'[i] \notin MinimalElts(After)
                           THEN << >> 
                           ELSE <<p'[i]>> \o ToAdd(i+1, RemoveFrom({p'[i]}, After))
                       TA == ToAdd(Len(Q)+1, RemoveFrom(SeqElts(Q), after'))
                   IN  IF TA # << >>
                         THEN SetStutter("BeginEnq", e, TA) 
                         ELSE s' = s
               /\ Assign(enqInner, e, Busy)
               /\ UNCHANGED <<Q, deqInner>>
                 
BeginEnqIDo(e) == /\ PostStutterEnabled("BeginEnq", e)
                  /\ Q' = Append(Q, Head(s.val))
                  /\ Assign(enqInner, Writer(Head(s.val)), Done)
                  /\ IF Tail(s.val) # << >> THEN SetStutter("BeginEnq", e, Tail(s.val))
                                            ELSE s' = top
                  /\ UNCHANGED <<vars, p, deqInner>>
                  
DoEnqI(e) == /\ PreStutterEnabled("EndEnq", e)
             /\ enq[e] # Done 
             /\ IF enqInner[e] # Done \* adding[e] \notin SeqElts(Q)
                 THEN /\ Q' = Append(Q, adding[e])
                      /\ Assign(enqInner, e, Done)
                 ELSE UNCHANGED <<Q, enqInner>>
             /\ SetStutter("EndEnq", e, TRUE)
             /\ UNCHANGED <<vars, p, deqInner>>
                              
EndEnqI(e) ==  /\ AfterPreStutterEnabled("EndEnq", e) 
               /\ EndEnq(e) 
               /\ s' = top
               /\ UNCHANGED << p, Q, enqInner, deqInner>>

BeginDeqI(d) == /\ AllEnabled
                /\ BeginDeq(d) 
                /\ Assign(deqInner, d, NoData)
                /\ UNCHANGED <<p, Q, s, enqInner>>

\* OLD DEFS:
\*DoDeqI(d) == /\ PreStutterEnabled("EndDeq", d)
\*             /\ deq[d] = Busy
\*             /\ minimalElts # {}
\*             /\ IF s = top /\ Q = << >>
\*                  THEN /\ \E el \in minimalElts : 
\*                             /\ Q' = <<el>>
\*                             /\ Assign(enqInner, Writer(el), Done)                      
\*                       /\ SetStutter("EndDeq", d, FALSE)
\*                       /\ UNCHANGED deqInner
\*                  ELSE /\ Q' = Tail(Q)
\*                       /\ SetStutter("EndDeq", d, TRUE)
\*                       /\ Assign(deqInner, d, Head(Q))
\*                       /\ UNCHANGED enqInner
\*             /\ UNCHANGED <<vars, p>>
\*
\*EndDeqI(d) == /\ AfterPreStutterEnabled("EndDeq", d) 
\*              /\ EndDeq(d) 
\*              /\ p = << >> \/ Head(p) = deqInner[d]
\*              /\ p' = Tail(p)
\*              /\ s' = top
\*              /\ UNCHANGED <<Q, enqInner, deqInner>>
(***************************************************************************
XEndDeq(d, el) defined so that

   EndDeq(d) == \E el \in Elements : XEndDeq(d, el)
 ***************************************************************************)
XEndDeq(d, el) == /\ deq[d] = Busy
                  /\ el \in minimalElts
                  /\ RemoveElt(el)
                  /\ Assign(deq, d, el.data)
             /\ UNCHANGED <<enq, adding>>

DoDeqI(d, el) == /\ PreStutterEnabled("EndDeq", <<d, el>>)
                 /\ deq[d] = Busy
                 /\ el \in minimalElts
                 /\  \/ p = << >> /\ p' = << >> /\ Assert(FALSE, "shouldn't happen")
                     \/ Head(p) = el /\ p' = Tail(p)
                 /\ IF s = top /\ Q = << >>
                      THEN \* I believe this case should never occur
                           /\ Q' = <<el>>
                           /\ Assign(enqInner, Writer(el), Done)                      
                           /\ SetStutter("EndDeq", <<d, el>>,  FALSE)
                           /\ UNCHANGED deqInner
                      ELSE /\ el = Head(Q)
                           /\ Q' = Tail(Q)
                           /\ SetStutter("EndDeq", <<d, el>>, TRUE)
                           /\ Assign(deqInner, d, Head(Q))
                           /\ UNCHANGED enqInner
                 /\ UNCHANGED <<vars>>

EndDeqI(d, el) == /\ AfterPreStutterEnabled("EndDeq", <<d, el>>) 
                  /\ XEndDeq(d, el) 
\*                  /\ p = << >> \/ Head(p) = deqInner[d]
\*                  /\ p' = Tail(p)
                  /\ s' = top
                  /\ UNCHANGED <<Q, enqInner, deqInner, p>>

NextI == \/ \E e \in EnQers : BeginEnqI(e) \/ BeginEnqIDo(e) 
                                  \/ DoEnqI(e) \/ EndEnqI(e)
         \/ \E d \in DeQers : \/ BeginDeqI(d) 
                              \/ \E el \in Elements : DoDeqI(d, el) \/ EndDeqI(d, el)

SpecI == InitI /\ [][NextI]_varsI    
-----------------------------------------------------------------------------
queue == [i \in 1..Len(Q) |-> Q[i].data]

deqInnerBar == [d \in DeQers |-> IF deqInner[d] = NoData THEN NoData
                                                         ELSE deqInner[d].data]
I == INSTANCE QSpec WITH deqInner <- deqInnerBar
            
=============================================================================
\* Modification History
\* Last modified Sat Nov 14 17:54:40 PST 2015 by lamport
\* Created Fri Nov 06 11:05:33 PST 2015 by lamport
