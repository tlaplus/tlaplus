------------------------ MODULE LiveWriteThroughCache ----------------------- 
(***************************************************************************)
(* This module adds the liveness condition described in the section "The   *)
(* Write-Through Cache" to the specification Spec of module                *)
(* WriteThroughCache.  To allow us to check it with TLC, we actually use   *)
(* the equivalent definition of Spec from module                           *)
(* WriteThroughCacheInstanced.                                             *)
(***************************************************************************)

EXTENDS WriteThroughCacheInstanced

vars == <<memInt, wmem, buf, ctl, cache, memQ>>

QCond == \/ Len(memQ) = QLen
         \/ \E i \in 1 .. Len(memQ) : memQ[i][2].op = "Rd"

Liveness == /\ \A p \in Proc : /\ WF_vars(Rsp(p) \/ DoRd(p))
                               /\ SF_vars(RdMiss(p) \/ DoWr(p))
            /\ WF_vars((QCond /\ MemQWr) \/ MemQRd)

LSpec == Spec /\ Liveness

=============================================================================

Liveness == /\ \A p \in Proc : /\ WF_vars(Rsp(p) \/ DoRd(p))
                               /\ SF_vars(RdMiss(p) \/ DoWr(p))
            /\ WF_vars(MemQWr \/ MemQRd)

