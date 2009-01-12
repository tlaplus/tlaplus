--------------------- MODULE RTMemory ----------------------
EXTENDS MemoryInterface, RealTime
CONSTANT Rho
ASSUME (Rho \in Real) /\ (Rho > 0)
 
   ---------------- MODULE Inner ----------------------------------
   EXTENDS InternalMemory
   Respond(p) == (ctl[p] # "rdy") /\ (ctl'[p] = "rdy")
   RTISpec == /\ ISpec
              /\ \A p \in Proc : RTBound(Respond(p), ctl, 0, Rho)
              /\ RTnow(<<memInt, mem, ctl, buf>>)
   ==========================================================

Inner1(mem, ctl, buf) == INSTANCE Inner
RTSpec == \EE mem, ctl, buf : Inner1(mem, ctl, buf)!RTISpec
=============================================================
