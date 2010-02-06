
------------------------- MODULE MCRealTimeHourClock --------------------------
EXTENDS Naturals, HourClock 
VARIABLE now 
CONSTANT Rho, MaxReal, SecondsPerHour
-----------------------------------------------------------------------------

Real == 0 .. MaxReal

ASSUME (Rho \in Real) /\  (Rho > 0) 

   VARIABLE t  
   TNext == t' = IF HCnxt THEN 0 ELSE t+(now'-now) 
   IsTimer == (t = 0)  /\  [][TNext]_<<t,hr,now>>
   MaxTime == [](t \leq  SecondsPerHour + Rho)  
   MinTime == [][HCnxt => t \geq SecondsPerHour - Rho]_hr
   HCTime == IsTimer /\ MaxTime /\ MinTime 


NowNext == /\ now' \in {r \in Real : r > now} 
           /\ UNCHANGED hr  

BigNext == /\ [NowNext]_now
           /\ [HCnxt]_hr
           /\ TNext
           /\ HCnxt => t \geq SecondsPerHour - Rho
           /\ t' \leq  SecondsPerHour + Rho

BigInit == /\ HCini
           /\ t = 0
           /\ now \in Real 

Fairness == \A r \in Real : WF_now(NowNext /\ (now'>r))

NonZeno == \A r \in Real : <>(now \geq r)

ImpliedTemporal == \A h \in 1..12 : []<>(hr = h)

RT == /\ now \in Real 
      /\ [][NowNext]_now
      /\ \A r \in Real : WF_now(NowNext /\ (now'>r))

ErrorTemporal == []((now # 4) => <>[](now # 4))
=============================================================================
 