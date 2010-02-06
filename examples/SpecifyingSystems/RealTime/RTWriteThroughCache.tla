----------------------- MODULE RTWriteThroughCache --------------------------
EXTENDS WriteThroughCache, RealTime

CONSTANT N
ASSUME (N \in Nat) /\ (Proc = 0 .. N-1)

CONSTANTS Delta, Epsilon, Rho

ASSUME /\ (Delta \in Real)   /\ (Delta > 0)
       /\ (Epsilon \in Real) /\ (Epsilon > 0)
       /\ (Rho \in Real)     /\ (Rho > 0)
       /\ 2*(N+1)*Epsilon + (N+QLen)*Delta \leq Rho
-----------------------------------------------------------------------------
VARIABLE lastP

RTInit == Init /\ (lastP \in Proc)

position(p) == CHOOSE i \in 1 .. N : p = (lastP + i) % N

canGoNext(p) == 
   \A q \in Proc : (position(q) < position(p))
            =>  ~ENABLED(RdMiss(q) \/ DoWr(q))     

RTRdMiss(p) == /\ canGoNext(p)
               /\ RdMiss(p) 
               /\ lastP' = p    

RTDoWr(p)   == /\ canGoNext(p)
               /\ DoWr(p) 
               /\ lastP' = p    

RTNext ==
    \/ \E p\in Proc : RTRdMiss(p) \/ RTDoWr(p)
    \/ /\ \/ \E p\in Proc : \/ Req(p) \/ Rsp(p) \/ DoRd(p) 
                            \/ \E a \in Adr : Evict(p, a)
          \/ MemQWr \/ MemQRd    
       /\ UNCHANGED lastP

vars == <<memInt, wmem, buf, ctl, cache, memQ, lastP>>

RTSpec == /\ RTInit /\ [][RTNext]_vars
          /\ RTBound(MemQWr \/ MemQRd, vars, 0, Delta)
          /\ \A p \in Proc :
                /\ RTBound(RTDoWr(p) \/ DoRd(p) \/ Rsp(p),
                        vars, 0, Epsilon)
                /\ RTBound(RTRdMiss(p), vars, 0, Epsilon)
          /\ RTnow(vars)
-----------------------------------------------------------------------------
RTM == INSTANCE RTMemory 
THEOREM RTSpec => RTM!Spec
=============================================================================
