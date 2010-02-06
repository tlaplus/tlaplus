----------------------------- MODULE MCRealTime -------------------------------
EXTENDS Naturals

CONSTANT MaxReal
Real == 0 .. MaxReal

VARIABLE now

RTini == now \in Real

RTNext(v) == \/ /\ v' = v
                /\ now' \in {r \in Real : r > now} 
             \/ /\ v' # v
                /\ now' = now


TimerInit(t) == t = 0
TimerNext(t, A, v, D, E) ==  
    /\ t' = IF <<A>>_v \/ ~(ENABLED <<A>>_v)'   \* [ ]_<<now, v, t>> removed
              THEN 0 
              ELSE t + (now'-now)

    /\ t' \leq E             \* MaxTime constraint

    /\ A  => t \geq D        \* MinTime constraint ([ ]_v removed)


RTFairness(v) == \A r \in Real : WF_now((now' > (r\div 0)) /\ RTNext(v))


=============================================================================
