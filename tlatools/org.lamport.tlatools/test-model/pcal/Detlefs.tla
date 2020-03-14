------------------------------- MODULE Detlefs ------------------------------ 
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS Val, Address, Dummy, Procs, GC
ASSUME Dummy \in Address
ASSUME GC \notin Procs


null == CHOOSE n: n \notin Address
Node == [R : Address \cup {null}, L : Address \cup {null}, V : Val]
DummyNode == [R |-> Dummy, L |-> Dummy, V |-> null]
InitNode ==  [R |-> null,  L |-> null,  V |-> null]

(*
\* boolean DCAS(val *addr1, val *addr2, 
\*              val old1, val old2, 
\*              val new1, val new2) { 
\*  atomically { 
\*    if (( *addr1 == old1) && 
\*        ( *addr2 == old2)) { 
\*      *addr1 = new1; 
\*      *addr2 = new2; 
\*      return true; 
\*    } else return false; } }

--algorithm Snark {
variables Mem = [i \in Address |-> IF i = Dummy THEN DummyNode ELSE InitNode],
          freeList = Address \ {Dummy},
          LeftHat  = Dummy,
          RightHat = Dummy,
          rVal = [i \in Procs |-> "okay"] ,   \* Used for returning values
          valBag = [i \in Val |-> 0] ;
            \* For testing: valBag[i] is the number of copies of i 
            \* that can be in the queue.

macro New(result) {
  if (freeList # {}) {
    result := CHOOSE a \in freeList : TRUE ;
    freeList := freeList \ {result} ;
  } else result := null
}

macro DCAS(result, addr1, addr2, old1, old2, new1, new2) {
  if ( /\ addr1 = old1
       /\ addr2 = old2) { 
    addr1 := new1 ||
    addr2 := new2 ;
    result := TRUE; 
  } else result := FALSE; } 


\* val pushRight(val v) { 
\*   nd = new Node(); /* Allocate new Node structure */ 
\*   if (nd == null) return "full"; 
\*   nd�>R = Dummy; 
\*   nd�>V = v; 
\*   while (true) { 
\*     rh = RightHat;                           /* Labels A, B,   */ 
\*     rhR = rh�>R;                             /* etc., are used */ 
\*     if (rhR == rh) {                         /* in the proof   */ 
\*       nd�>L = Dummy;                         /* of correctness */ 
\*       lh = LeftHat; 
\*       if (DCAS(&RightHat, &LeftHat, rh, lh, nd, nd))      /* A */ 
\*         return "okay"; 
\*     } else { 
\*       nd�>L = rh; 
\*       if (DCAS(&RightHat, &rh�>R, rh, rhR, nd, nd))      /* B */ 
\*         return "okay"; 
\* } } } // Please forgive this brace style 

procedure pushRight(v) 
 variables nd = null , rh = Dummy, rhR = Dummy, lh = Dummy, 
           temp = Dummy ; { 
L1: New(nd) ; 
    if (nd = null) { rVal[self] := "full"; L1a: return } ;
L1b: Mem[nd].R := Dummy ||   \* Since no other thread can access nd here,
     Mem[nd].V := v ; 
L4: while (TRUE) { 
      rh  := RightHat;                           
L5:   rhR := Mem[rh].R;                          
L6:   if (rhR = rh) {                         
        Mem[nd].L := Dummy;                   
        lh := LeftHat; 
L7:     DCAS(temp, RightHat, LeftHat, rh, lh, nd, nd) ;
        if (temp) { 
          rVal[self] := "okay"; L7a: return}
      } else { 
L8:       Mem[nd].L := rh; 
L9:       DCAS(temp, RightHat, Mem[rh].R, rh, rhR, nd, nd) ;
          if (temp) {
            rVal[self] := "okay";  L8a: return }
} } } 


\* val popRight() { 
\*    while (true) { 
\*      rh = RightHat;                     // Delicate order of operations 
\*      lh = LeftHat;                      // here (see proof of Theorem 4 
\*      if (rh�>R == rh) return "empty";   // and the Conclusions section) 
\*      if (rh == lh) { 
\*        if (DCAS(&RightHat, &LeftHat, rh, lh, Dummy, Dummy))     /* C */ 
\*          return rh�>V; 
\*      } else { 
\*        rhL = rh�>L; 
\*        if (DCAS(&RightHat, &rh�>L, rh, rhL, rhL, rh)) {         /* D */ 
\*          result = rh�>V; 
\*          rh�>R = Dummy; /* E */ 
\*          rh�>V = null;                        /* optional (see text) */ 
\*          return result; 
\* } } } }                         // Stacking braces this way saves space 
\* 

procedure popRight()
 variables rh = Dummy, lh = Dummy, rhL = Dummy, 
           temp = Dummy , result = null ; { 
M1: while (TRUE) { 
      rh := RightHat;    
M2:   lh := LeftHat;     
      if (Mem[rh].R = rh) {rVal[self] := "empty"; M2a: return ;} ;
M3:   if (rh = lh) { 
        DCAS(temp, RightHat, LeftHat, rh, lh, Dummy, Dummy) ;
        if (temp) { 
M4:       rVal[self] := Mem[rh].V ; M4a:  return;} 
      } else { 
M5:     rhL := Mem[rh].L ; 
M6:     DCAS(temp, RightHat, Mem[rh].L, rh, rhL, rhL, rh) ;
        if (temp) {         
M7:       result := Mem[rh].V; 
M8:       Mem[rh].R := Dummy ||
          Mem[rh].V := null;  
          rVal[self] := result ; M9a: return ;
} } } }

\* val pushLeft(val v) { 
\*   nd = new Node();      /* Allocate new Node structure */ 
\*   if (nd == null) return "full"; 
\*   nd�>L = Dummy; 
\*   nd�>V = v; 
\*   while (true) { 
\*     lh = LeftHat; 
\*     lhL = lh�>L; 
\*     if (lhL == lh) { 
\*       nd�>R = Dummy; 
\*       rh = RightHat; 
\*       if (DCAS(&LeftHat, &RightHat, lh, rh, nd, nd))          /* A' */ 
\*         return "okay"; 
\*     } else { 
\*       nd�>R = lh; 
\*       if (DCAS(&LeftHat, &lh�>L, lh, lhL, nd, nd))            /* B' */ 
\*         return "okay"; 
\* } } }                        // We were given a firm limit of 15 pages 

procedure pushLeft(v) 
 variables nd = null , rh = Dummy, lhL = Dummy, lh = Dummy, 
           temp = Dummy ; { 
N1: New(nd) ;                          
    if (nd = null) {rVal[self] := "full"; N1a: return ;} ;
N1b: Mem[nd].L := Dummy ||   \* Since no other thread can access nd here,
    Mem[nd].V := v;          \* we can represent this as a single action. 
N2: while (TRUE) { 
    lh := LeftHat;          
N3: lhL := Mem[lh].L; 
    if (lhL = lh) { 
N4:   Mem[nd].R := Dummy; 
N5:   rh := RightHat; 
N6:   DCAS(temp, LeftHat, RightHat, lh, rh, nd, nd) ;
      if (temp) {          
        rVal[self] := "okay";  nd := null ; N6a: return;}
    } else { 
N7:   Mem[nd].R := lh; 
N8:   DCAS(temp, LeftHat, Mem[lh].L, lh, lhL, nd, nd) ;
      if (temp) {          
        rVal[self] := "okay"; nd := null ; N8a: return }
} } }                    
  
\* val popLeft() { 
\*   while (true) { 
\*     lh = LeftHat;                          // Delicate order of operations 
\*     rh = RightHat;                         // here (see proof of Theorem 4 
\*     if (lh�>L == lh) return "empty";       // and the Conclusions section) 
\*     if (lh == rh) { 
\*       if (DCAS(&LeftHat, &RightHat, lh, rh, Dummy, Dummy))        /* C' */ 
\*         return lh�>V; 
\*     } else { 
\*       lhR = lh�>R; 
\*       if (DCAS(&LeftHat, &lh�>R, lh, lhR, lhR, lh)) {             /* D' */ 
\*         result = lh�>V; 
\*         lh�>L = Dummy;                                            /* E' */ 
\*         lh�>V = null;                            /* optional (see text) */ 
\*         return result; 
\* } } } }                     // Better to stack braces than to omit a lemma 

procedure popLeft() 
 variables rh = Dummy, lh = Dummy, lhR = Dummy, 
           temp = Dummy , result = null ; { 
O1: while (TRUE) { 
      lh := LeftHat;                           
O2:   rh := RightHat;                    
O3:   if (Mem[lh].L = lh) {rVal[self] := "empty";  O3a: return ;} ;
O4:   if (lh = rh) { 
      DCAS(temp, LeftHat, RightHat, lh, rh, Dummy, Dummy) ;
      if (temp) {          
O5:     rVal[self] := Mem[lh].V; O5a: return; }
      } else { 
O6:     lhR := Mem[lh].R; 
O7:     DCAS(temp, LeftHat, Mem[lh].R, lh, lhR, lhR, lh) ;
      if (temp) {               
O8:     result := Mem[lh].V; 
O9:     Mem[lh].L := Dummy ||
        Mem[lh].V := null;                              
        rVal[self] := result;  O10a: return ;
} } } }                       


\* process (GarbageCollet = GC) {
\* GC1: while (TRUE) {
\*      with (adr \in Address \ (freeList \cup {Dummy})) {
\*        when Mem[adr].canGC ;
\*        when \A b \in Address \ (freeList \cup {Dummy, adr}) :
\*               /\ adr # Mem[b].L
\*               /\ adr # Mem[b].R ;
\*        freeList := freeList \cup {adr} ;
\*        Mem[adr] := InitNode;
\*      } } }

process (test \in Procs)
variables pushedVal = null ; {
T1: while(TRUE) {
      either { \* push
        with (x \in Val) {pushedVal := x} ;
        valBag[pushedVal] := valBag[pushedVal] + 1 ;
        either  call pushLeft(pushedVal) or call pushRight(pushedVal)  ;
T2:     if (rVal[self] = "full") valBag[pushedVal] := valBag[pushedVal] - 1 
        }
      or { \* pop
        either call popLeft() or call popRight()  ;
T3:     if (rVal[self] # "empty") {
          assert valBag[rVal[self]] > 0 ;
          valBag[rVal[self]] := valBag[rVal[self]] - 1;
        } 
} } }}
*)

\* BEGIN TRANSLATION
\* Procedure variable nd of procedure pushRight at line 72 col 12 changed to nd_
\* Procedure variable rh of procedure pushRight at line 72 col 24 changed to rh_
\* Procedure variable lh of procedure pushRight at line 72 col 49 changed to lh_
\* Procedure variable temp of procedure pushRight at line 73 col 12 changed to temp_
\* Procedure variable rh of procedure popRight at line 114 col 12 changed to rh_p
\* Procedure variable lh of procedure popRight at line 114 col 24 changed to lh_p
\* Procedure variable temp of procedure popRight at line 115 col 12 changed to temp_p
\* Procedure variable result of procedure popRight at line 115 col 27 changed to result_
\* Procedure variable rh of procedure pushLeft at line 154 col 24 changed to rh_pu
\* Procedure variable lh of procedure pushLeft at line 154 col 49 changed to lh_pu
\* Procedure variable temp of procedure pushLeft at line 155 col 12 changed to temp_pu
\* Parameter v of procedure pushRight at line 71 col 21 changed to v_
CONSTANT defaultInitValue
VARIABLES Mem, freeList, LeftHat, RightHat, rVal, valBag, pc, stack, v_, nd_, 
          rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, temp_p, result_, v, nd, 
          rh_pu, lhL, lh_pu, temp_pu, rh, lh, lhR, temp, result, pushedVal

vars == << Mem, freeList, LeftHat, RightHat, rVal, valBag, pc, stack, v_, nd_, 
           rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, temp_p, result_, v, nd, 
           rh_pu, lhL, lh_pu, temp_pu, rh, lh, lhR, temp, result, pushedVal
        >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ Mem = [i \in Address |-> IF i = Dummy THEN DummyNode ELSE InitNode]
        /\ freeList = Address \ {Dummy}
        /\ LeftHat = Dummy
        /\ RightHat = Dummy
        /\ rVal = [i \in Procs |-> "okay"]
        /\ valBag = [i \in Val |-> 0]
        (* Procedure pushRight *)
        /\ v_ = [ self \in ProcSet |-> defaultInitValue]
        /\ nd_ = [ self \in ProcSet |-> null]
        /\ rh_ = [ self \in ProcSet |-> Dummy]
        /\ rhR = [ self \in ProcSet |-> Dummy]
        /\ lh_ = [ self \in ProcSet |-> Dummy]
        /\ temp_ = [ self \in ProcSet |-> Dummy]
        (* Procedure popRight *)
        /\ rh_p = [ self \in ProcSet |-> Dummy]
        /\ lh_p = [ self \in ProcSet |-> Dummy]
        /\ rhL = [ self \in ProcSet |-> Dummy]
        /\ temp_p = [ self \in ProcSet |-> Dummy]
        /\ result_ = [ self \in ProcSet |-> null]
        (* Procedure pushLeft *)
        /\ v = [ self \in ProcSet |-> defaultInitValue]
        /\ nd = [ self \in ProcSet |-> null]
        /\ rh_pu = [ self \in ProcSet |-> Dummy]
        /\ lhL = [ self \in ProcSet |-> Dummy]
        /\ lh_pu = [ self \in ProcSet |-> Dummy]
        /\ temp_pu = [ self \in ProcSet |-> Dummy]
        (* Procedure popLeft *)
        /\ rh = [ self \in ProcSet |-> Dummy]
        /\ lh = [ self \in ProcSet |-> Dummy]
        /\ lhR = [ self \in ProcSet |-> Dummy]
        /\ temp = [ self \in ProcSet |-> Dummy]
        /\ result = [ self \in ProcSet |-> null]
        (* Process test *)
        /\ pushedVal = [self \in Procs |-> null]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "T1"]

L1(self) == /\ pc[self] = "L1"
            /\ IF freeList # {}
                  THEN /\ nd_' = [nd_ EXCEPT ![self] = CHOOSE a \in freeList : TRUE]
                       /\ freeList' = freeList \ {nd_'[self]}
                  ELSE /\ nd_' = [nd_ EXCEPT ![self] = null]
                       /\ UNCHANGED freeList
            /\ IF nd_'[self] = null
                  THEN /\ rVal' = [rVal EXCEPT ![self] = "full"]
                       /\ pc' = [pc EXCEPT ![self] = "L1a"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L1b"]
                       /\ rVal' = rVal
            /\ UNCHANGED << Mem, LeftHat, RightHat, valBag, stack, v_, rh_, 
                            rhR, lh_, temp_, rh_p, lh_p, rhL, temp_p, result_, 
                            v, nd, rh_pu, lhL, lh_pu, temp_pu, rh, lh, lhR, 
                            temp, result, pushedVal >>

L1a(self) == /\ pc[self] = "L1a"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ nd_' = [nd_ EXCEPT ![self] = Head(stack[self]).nd_]
             /\ rh_' = [rh_ EXCEPT ![self] = Head(stack[self]).rh_]
             /\ rhR' = [rhR EXCEPT ![self] = Head(stack[self]).rhR]
             /\ lh_' = [lh_ EXCEPT ![self] = Head(stack[self]).lh_]
             /\ temp_' = [temp_ EXCEPT ![self] = Head(stack[self]).temp_]
             /\ v_' = [v_ EXCEPT ![self] = Head(stack[self]).v_]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                             rh_p, lh_p, rhL, temp_p, result_, v, nd, rh_pu, 
                             lhL, lh_pu, temp_pu, rh, lh, lhR, temp, result, 
                             pushedVal >>

L1b(self) == /\ pc[self] = "L1b"
             /\ Mem' = [Mem EXCEPT ![nd_[self]].R = Dummy,
                                   ![nd_[self]].V = v_[self]]
             /\ pc' = [pc EXCEPT ![self] = "L4"]
             /\ UNCHANGED << freeList, LeftHat, RightHat, rVal, valBag, stack, 
                             v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                             temp_p, result_, v, nd, rh_pu, lhL, lh_pu, 
                             temp_pu, rh, lh, lhR, temp, result, pushedVal >>

L4(self) == /\ pc[self] = "L4"
            /\ rh_' = [rh_ EXCEPT ![self] = RightHat]
            /\ pc' = [pc EXCEPT ![self] = "L5"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                            temp_p, result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

L5(self) == /\ pc[self] = "L5"
            /\ rhR' = [rhR EXCEPT ![self] = Mem[rh_[self]].R]
            /\ pc' = [pc EXCEPT ![self] = "L6"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rh_, lh_, temp_, rh_p, lh_p, rhL, 
                            temp_p, result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

L6(self) == /\ pc[self] = "L6"
            /\ IF rhR[self] = rh_[self]
                  THEN /\ Mem' = [Mem EXCEPT ![nd_[self]].L = Dummy]
                       /\ lh_' = [lh_ EXCEPT ![self] = LeftHat]
                       /\ pc' = [pc EXCEPT ![self] = "L7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L8"]
                       /\ UNCHANGED << Mem, lh_ >>
            /\ UNCHANGED << freeList, LeftHat, RightHat, rVal, valBag, stack, 
                            v_, nd_, rh_, rhR, temp_, rh_p, lh_p, rhL, temp_p, 
                            result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, rh, lh, 
                            lhR, temp, result, pushedVal >>

L7(self) == /\ pc[self] = "L7"
            /\ IF /\ RightHat = rh_[self]
                  /\ LeftHat = lh_[self]
                  THEN /\ /\ LeftHat' = nd_[self]
                          /\ RightHat' = nd_[self]
                       /\ temp_' = [temp_ EXCEPT ![self] = TRUE]
                  ELSE /\ temp_' = [temp_ EXCEPT ![self] = FALSE]
                       /\ UNCHANGED << LeftHat, RightHat >>
            /\ IF temp_'[self]
                  THEN /\ rVal' = [rVal EXCEPT ![self] = "okay"]
                       /\ pc' = [pc EXCEPT ![self] = "L7a"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L4"]
                       /\ rVal' = rVal
            /\ UNCHANGED << Mem, freeList, valBag, stack, v_, nd_, rh_, rhR, 
                            lh_, rh_p, lh_p, rhL, temp_p, result_, v, nd, 
                            rh_pu, lhL, lh_pu, temp_pu, rh, lh, lhR, temp, 
                            result, pushedVal >>

L7a(self) == /\ pc[self] = "L7a"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ nd_' = [nd_ EXCEPT ![self] = Head(stack[self]).nd_]
             /\ rh_' = [rh_ EXCEPT ![self] = Head(stack[self]).rh_]
             /\ rhR' = [rhR EXCEPT ![self] = Head(stack[self]).rhR]
             /\ lh_' = [lh_ EXCEPT ![self] = Head(stack[self]).lh_]
             /\ temp_' = [temp_ EXCEPT ![self] = Head(stack[self]).temp_]
             /\ v_' = [v_ EXCEPT ![self] = Head(stack[self]).v_]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                             rh_p, lh_p, rhL, temp_p, result_, v, nd, rh_pu, 
                             lhL, lh_pu, temp_pu, rh, lh, lhR, temp, result, 
                             pushedVal >>

L8(self) == /\ pc[self] = "L8"
            /\ Mem' = [Mem EXCEPT ![nd_[self]].L = rh_[self]]
            /\ pc' = [pc EXCEPT ![self] = "L9"]
            /\ UNCHANGED << freeList, LeftHat, RightHat, rVal, valBag, stack, 
                            v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                            temp_p, result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

L9(self) == /\ pc[self] = "L9"
            /\ IF /\ RightHat = rh_[self]
                  /\ (Mem[rh_[self]].R) = rhR[self]
                  THEN /\ /\ Mem' = [Mem EXCEPT ![rh_[self]].R = nd_[self]]
                          /\ RightHat' = nd_[self]
                       /\ temp_' = [temp_ EXCEPT ![self] = TRUE]
                  ELSE /\ temp_' = [temp_ EXCEPT ![self] = FALSE]
                       /\ UNCHANGED << Mem, RightHat >>
            /\ IF temp_'[self]
                  THEN /\ rVal' = [rVal EXCEPT ![self] = "okay"]
                       /\ pc' = [pc EXCEPT ![self] = "L8a"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L4"]
                       /\ rVal' = rVal
            /\ UNCHANGED << freeList, LeftHat, valBag, stack, v_, nd_, rh_, 
                            rhR, lh_, rh_p, lh_p, rhL, temp_p, result_, v, nd, 
                            rh_pu, lhL, lh_pu, temp_pu, rh, lh, lhR, temp, 
                            result, pushedVal >>

L8a(self) == /\ pc[self] = "L8a"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ nd_' = [nd_ EXCEPT ![self] = Head(stack[self]).nd_]
             /\ rh_' = [rh_ EXCEPT ![self] = Head(stack[self]).rh_]
             /\ rhR' = [rhR EXCEPT ![self] = Head(stack[self]).rhR]
             /\ lh_' = [lh_ EXCEPT ![self] = Head(stack[self]).lh_]
             /\ temp_' = [temp_ EXCEPT ![self] = Head(stack[self]).temp_]
             /\ v_' = [v_ EXCEPT ![self] = Head(stack[self]).v_]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                             rh_p, lh_p, rhL, temp_p, result_, v, nd, rh_pu, 
                             lhL, lh_pu, temp_pu, rh, lh, lhR, temp, result, 
                             pushedVal >>

pushRight(self) == L1(self) \/ L1a(self) \/ L1b(self) \/ L4(self)
                      \/ L5(self) \/ L6(self) \/ L7(self) \/ L7a(self)
                      \/ L8(self) \/ L9(self) \/ L8a(self)

M1(self) == /\ pc[self] = "M1"
            /\ rh_p' = [rh_p EXCEPT ![self] = RightHat]
            /\ pc' = [pc EXCEPT ![self] = "M2"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rh_, rhR, lh_, temp_, lh_p, rhL, 
                            temp_p, result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

M2(self) == /\ pc[self] = "M2"
            /\ lh_p' = [lh_p EXCEPT ![self] = LeftHat]
            /\ IF Mem[rh_p[self]].R = rh_p[self]
                  THEN /\ rVal' = [rVal EXCEPT ![self] = "empty"]
                       /\ pc' = [pc EXCEPT ![self] = "M2a"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "M3"]
                       /\ rVal' = rVal
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag, stack, 
                            v_, nd_, rh_, rhR, lh_, temp_, rh_p, rhL, temp_p, 
                            result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, rh, lh, 
                            lhR, temp, result, pushedVal >>

M2a(self) == /\ pc[self] = "M2a"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ rh_p' = [rh_p EXCEPT ![self] = Head(stack[self]).rh_p]
             /\ lh_p' = [lh_p EXCEPT ![self] = Head(stack[self]).lh_p]
             /\ rhL' = [rhL EXCEPT ![self] = Head(stack[self]).rhL]
             /\ temp_p' = [temp_p EXCEPT ![self] = Head(stack[self]).temp_p]
             /\ result_' = [result_ EXCEPT ![self] = Head(stack[self]).result_]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                             v_, nd_, rh_, rhR, lh_, temp_, v, nd, rh_pu, lhL, 
                             lh_pu, temp_pu, rh, lh, lhR, temp, result, 
                             pushedVal >>

M3(self) == /\ pc[self] = "M3"
            /\ IF rh_p[self] = lh_p[self]
                  THEN /\ IF /\ RightHat = rh_p[self]
                             /\ LeftHat = lh_p[self]
                             THEN /\ /\ LeftHat' = Dummy
                                     /\ RightHat' = Dummy
                                  /\ temp_p' = [temp_p EXCEPT ![self] = TRUE]
                             ELSE /\ temp_p' = [temp_p EXCEPT ![self] = FALSE]
                                  /\ UNCHANGED << LeftHat, RightHat >>
                       /\ IF temp_p'[self]
                             THEN /\ pc' = [pc EXCEPT ![self] = "M4"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "M1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "M5"]
                       /\ UNCHANGED << LeftHat, RightHat, temp_p >>
            /\ UNCHANGED << Mem, freeList, rVal, valBag, stack, v_, nd_, rh_, 
                            rhR, lh_, temp_, rh_p, lh_p, rhL, result_, v, nd, 
                            rh_pu, lhL, lh_pu, temp_pu, rh, lh, lhR, temp, 
                            result, pushedVal >>

M5(self) == /\ pc[self] = "M5"
            /\ rhL' = [rhL EXCEPT ![self] = Mem[rh_p[self]].L]
            /\ pc' = [pc EXCEPT ![self] = "M6"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, 
                            temp_p, result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

M6(self) == /\ pc[self] = "M6"
            /\ IF /\ RightHat = rh_p[self]
                  /\ (Mem[rh_p[self]].L) = rhL[self]
                  THEN /\ /\ Mem' = [Mem EXCEPT ![rh_p[self]].L = rh_p[self]]
                          /\ RightHat' = rhL[self]
                       /\ temp_p' = [temp_p EXCEPT ![self] = TRUE]
                  ELSE /\ temp_p' = [temp_p EXCEPT ![self] = FALSE]
                       /\ UNCHANGED << Mem, RightHat >>
            /\ IF temp_p'[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "M7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "M1"]
            /\ UNCHANGED << freeList, LeftHat, rVal, valBag, stack, v_, nd_, 
                            rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, result_, v, 
                            nd, rh_pu, lhL, lh_pu, temp_pu, rh, lh, lhR, temp, 
                            result, pushedVal >>

M7(self) == /\ pc[self] = "M7"
            /\ result_' = [result_ EXCEPT ![self] = Mem[rh_p[self]].V]
            /\ pc' = [pc EXCEPT ![self] = "M8"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, 
                            rhL, temp_p, v, nd, rh_pu, lhL, lh_pu, temp_pu, rh, 
                            lh, lhR, temp, result, pushedVal >>

M8(self) == /\ pc[self] = "M8"
            /\ Mem' = [Mem EXCEPT ![rh_p[self]].R = Dummy,
                                  ![rh_p[self]].V = null]
            /\ rVal' = [rVal EXCEPT ![self] = result_[self]]
            /\ pc' = [pc EXCEPT ![self] = "M9a"]
            /\ UNCHANGED << freeList, LeftHat, RightHat, valBag, stack, v_, 
                            nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, temp_p, 
                            result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, rh, lh, 
                            lhR, temp, result, pushedVal >>

M9a(self) == /\ pc[self] = "M9a"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ rh_p' = [rh_p EXCEPT ![self] = Head(stack[self]).rh_p]
             /\ lh_p' = [lh_p EXCEPT ![self] = Head(stack[self]).lh_p]
             /\ rhL' = [rhL EXCEPT ![self] = Head(stack[self]).rhL]
             /\ temp_p' = [temp_p EXCEPT ![self] = Head(stack[self]).temp_p]
             /\ result_' = [result_ EXCEPT ![self] = Head(stack[self]).result_]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                             v_, nd_, rh_, rhR, lh_, temp_, v, nd, rh_pu, lhL, 
                             lh_pu, temp_pu, rh, lh, lhR, temp, result, 
                             pushedVal >>

M4(self) == /\ pc[self] = "M4"
            /\ rVal' = [rVal EXCEPT ![self] = Mem[rh_p[self]].V]
            /\ pc' = [pc EXCEPT ![self] = "M4a"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag, stack, 
                            v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                            temp_p, result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

M4a(self) == /\ pc[self] = "M4a"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ rh_p' = [rh_p EXCEPT ![self] = Head(stack[self]).rh_p]
             /\ lh_p' = [lh_p EXCEPT ![self] = Head(stack[self]).lh_p]
             /\ rhL' = [rhL EXCEPT ![self] = Head(stack[self]).rhL]
             /\ temp_p' = [temp_p EXCEPT ![self] = Head(stack[self]).temp_p]
             /\ result_' = [result_ EXCEPT ![self] = Head(stack[self]).result_]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                             v_, nd_, rh_, rhR, lh_, temp_, v, nd, rh_pu, lhL, 
                             lh_pu, temp_pu, rh, lh, lhR, temp, result, 
                             pushedVal >>

popRight(self) == M1(self) \/ M2(self) \/ M2a(self) \/ M3(self) \/ M5(self)
                     \/ M6(self) \/ M7(self) \/ M8(self) \/ M9a(self)
                     \/ M4(self) \/ M4a(self)

N1(self) == /\ pc[self] = "N1"
            /\ IF freeList # {}
                  THEN /\ nd' = [nd EXCEPT ![self] = CHOOSE a \in freeList : TRUE]
                       /\ freeList' = freeList \ {nd'[self]}
                  ELSE /\ nd' = [nd EXCEPT ![self] = null]
                       /\ UNCHANGED freeList
            /\ IF nd'[self] = null
                  THEN /\ rVal' = [rVal EXCEPT ![self] = "full"]
                       /\ pc' = [pc EXCEPT ![self] = "N1a"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "N1b"]
                       /\ rVal' = rVal
            /\ UNCHANGED << Mem, LeftHat, RightHat, valBag, stack, v_, nd_, 
                            rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, temp_p, 
                            result_, v, rh_pu, lhL, lh_pu, temp_pu, rh, lh, 
                            lhR, temp, result, pushedVal >>

N1a(self) == /\ pc[self] = "N1a"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ nd' = [nd EXCEPT ![self] = Head(stack[self]).nd]
             /\ rh_pu' = [rh_pu EXCEPT ![self] = Head(stack[self]).rh_pu]
             /\ lhL' = [lhL EXCEPT ![self] = Head(stack[self]).lhL]
             /\ lh_pu' = [lh_pu EXCEPT ![self] = Head(stack[self]).lh_pu]
             /\ temp_pu' = [temp_pu EXCEPT ![self] = Head(stack[self]).temp_pu]
             /\ v' = [v EXCEPT ![self] = Head(stack[self]).v]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                             v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                             temp_p, result_, rh, lh, lhR, temp, result, 
                             pushedVal >>

N1b(self) == /\ pc[self] = "N1b"
             /\ Mem' = [Mem EXCEPT ![nd[self]].L = Dummy,
                                   ![nd[self]].V = v[self]]
             /\ pc' = [pc EXCEPT ![self] = "N2"]
             /\ UNCHANGED << freeList, LeftHat, RightHat, rVal, valBag, stack, 
                             v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                             temp_p, result_, v, nd, rh_pu, lhL, lh_pu, 
                             temp_pu, rh, lh, lhR, temp, result, pushedVal >>

N2(self) == /\ pc[self] = "N2"
            /\ lh_pu' = [lh_pu EXCEPT ![self] = LeftHat]
            /\ pc' = [pc EXCEPT ![self] = "N3"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, 
                            rhL, temp_p, result_, v, nd, rh_pu, lhL, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

N3(self) == /\ pc[self] = "N3"
            /\ lhL' = [lhL EXCEPT ![self] = Mem[lh_pu[self]].L]
            /\ IF lhL'[self] = lh_pu[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "N4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "N7"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, 
                            rhL, temp_p, result_, v, nd, rh_pu, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

N4(self) == /\ pc[self] = "N4"
            /\ Mem' = [Mem EXCEPT ![nd[self]].R = Dummy]
            /\ pc' = [pc EXCEPT ![self] = "N5"]
            /\ UNCHANGED << freeList, LeftHat, RightHat, rVal, valBag, stack, 
                            v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                            temp_p, result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

N5(self) == /\ pc[self] = "N5"
            /\ rh_pu' = [rh_pu EXCEPT ![self] = RightHat]
            /\ pc' = [pc EXCEPT ![self] = "N6"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, 
                            rhL, temp_p, result_, v, nd, lhL, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

N6(self) == /\ pc[self] = "N6"
            /\ IF /\ LeftHat = lh_pu[self]
                  /\ RightHat = rh_pu[self]
                  THEN /\ /\ LeftHat' = nd[self]
                          /\ RightHat' = nd[self]
                       /\ temp_pu' = [temp_pu EXCEPT ![self] = TRUE]
                  ELSE /\ temp_pu' = [temp_pu EXCEPT ![self] = FALSE]
                       /\ UNCHANGED << LeftHat, RightHat >>
            /\ IF temp_pu'[self]
                  THEN /\ rVal' = [rVal EXCEPT ![self] = "okay"]
                       /\ nd' = [nd EXCEPT ![self] = null]
                       /\ pc' = [pc EXCEPT ![self] = "N6a"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "N2"]
                       /\ UNCHANGED << rVal, nd >>
            /\ UNCHANGED << Mem, freeList, valBag, stack, v_, nd_, rh_, rhR, 
                            lh_, temp_, rh_p, lh_p, rhL, temp_p, result_, v, 
                            rh_pu, lhL, lh_pu, rh, lh, lhR, temp, result, 
                            pushedVal >>

N6a(self) == /\ pc[self] = "N6a"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ nd' = [nd EXCEPT ![self] = Head(stack[self]).nd]
             /\ rh_pu' = [rh_pu EXCEPT ![self] = Head(stack[self]).rh_pu]
             /\ lhL' = [lhL EXCEPT ![self] = Head(stack[self]).lhL]
             /\ lh_pu' = [lh_pu EXCEPT ![self] = Head(stack[self]).lh_pu]
             /\ temp_pu' = [temp_pu EXCEPT ![self] = Head(stack[self]).temp_pu]
             /\ v' = [v EXCEPT ![self] = Head(stack[self]).v]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                             v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                             temp_p, result_, rh, lh, lhR, temp, result, 
                             pushedVal >>

N7(self) == /\ pc[self] = "N7"
            /\ Mem' = [Mem EXCEPT ![nd[self]].R = lh_pu[self]]
            /\ pc' = [pc EXCEPT ![self] = "N8"]
            /\ UNCHANGED << freeList, LeftHat, RightHat, rVal, valBag, stack, 
                            v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                            temp_p, result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

N8(self) == /\ pc[self] = "N8"
            /\ IF /\ LeftHat = lh_pu[self]
                  /\ (Mem[lh_pu[self]].L) = lhL[self]
                  THEN /\ /\ LeftHat' = nd[self]
                          /\ Mem' = [Mem EXCEPT ![lh_pu[self]].L = nd[self]]
                       /\ temp_pu' = [temp_pu EXCEPT ![self] = TRUE]
                  ELSE /\ temp_pu' = [temp_pu EXCEPT ![self] = FALSE]
                       /\ UNCHANGED << Mem, LeftHat >>
            /\ IF temp_pu'[self]
                  THEN /\ rVal' = [rVal EXCEPT ![self] = "okay"]
                       /\ nd' = [nd EXCEPT ![self] = null]
                       /\ pc' = [pc EXCEPT ![self] = "N8a"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "N2"]
                       /\ UNCHANGED << rVal, nd >>
            /\ UNCHANGED << freeList, RightHat, valBag, stack, v_, nd_, rh_, 
                            rhR, lh_, temp_, rh_p, lh_p, rhL, temp_p, result_, 
                            v, rh_pu, lhL, lh_pu, rh, lh, lhR, temp, result, 
                            pushedVal >>

N8a(self) == /\ pc[self] = "N8a"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ nd' = [nd EXCEPT ![self] = Head(stack[self]).nd]
             /\ rh_pu' = [rh_pu EXCEPT ![self] = Head(stack[self]).rh_pu]
             /\ lhL' = [lhL EXCEPT ![self] = Head(stack[self]).lhL]
             /\ lh_pu' = [lh_pu EXCEPT ![self] = Head(stack[self]).lh_pu]
             /\ temp_pu' = [temp_pu EXCEPT ![self] = Head(stack[self]).temp_pu]
             /\ v' = [v EXCEPT ![self] = Head(stack[self]).v]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                             v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                             temp_p, result_, rh, lh, lhR, temp, result, 
                             pushedVal >>

pushLeft(self) == N1(self) \/ N1a(self) \/ N1b(self) \/ N2(self)
                     \/ N3(self) \/ N4(self) \/ N5(self) \/ N6(self)
                     \/ N6a(self) \/ N7(self) \/ N8(self) \/ N8a(self)

O1(self) == /\ pc[self] = "O1"
            /\ lh' = [lh EXCEPT ![self] = LeftHat]
            /\ pc' = [pc EXCEPT ![self] = "O2"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, 
                            rhL, temp_p, result_, v, nd, rh_pu, lhL, lh_pu, 
                            temp_pu, rh, lhR, temp, result, pushedVal >>

O2(self) == /\ pc[self] = "O2"
            /\ rh' = [rh EXCEPT ![self] = RightHat]
            /\ pc' = [pc EXCEPT ![self] = "O3"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, 
                            rhL, temp_p, result_, v, nd, rh_pu, lhL, lh_pu, 
                            temp_pu, lh, lhR, temp, result, pushedVal >>

O3(self) == /\ pc[self] = "O3"
            /\ IF Mem[lh[self]].L = lh[self]
                  THEN /\ rVal' = [rVal EXCEPT ![self] = "empty"]
                       /\ pc' = [pc EXCEPT ![self] = "O3a"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "O4"]
                       /\ rVal' = rVal
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag, stack, 
                            v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                            temp_p, result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

O3a(self) == /\ pc[self] = "O3a"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ rh' = [rh EXCEPT ![self] = Head(stack[self]).rh]
             /\ lh' = [lh EXCEPT ![self] = Head(stack[self]).lh]
             /\ lhR' = [lhR EXCEPT ![self] = Head(stack[self]).lhR]
             /\ temp' = [temp EXCEPT ![self] = Head(stack[self]).temp]
             /\ result' = [result EXCEPT ![self] = Head(stack[self]).result]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                             v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                             temp_p, result_, v, nd, rh_pu, lhL, lh_pu, 
                             temp_pu, pushedVal >>

O4(self) == /\ pc[self] = "O4"
            /\ IF lh[self] = rh[self]
                  THEN /\ IF /\ LeftHat = lh[self]
                             /\ RightHat = rh[self]
                             THEN /\ /\ LeftHat' = Dummy
                                     /\ RightHat' = Dummy
                                  /\ temp' = [temp EXCEPT ![self] = TRUE]
                             ELSE /\ temp' = [temp EXCEPT ![self] = FALSE]
                                  /\ UNCHANGED << LeftHat, RightHat >>
                       /\ IF temp'[self]
                             THEN /\ pc' = [pc EXCEPT ![self] = "O5"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "O1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "O6"]
                       /\ UNCHANGED << LeftHat, RightHat, temp >>
            /\ UNCHANGED << Mem, freeList, rVal, valBag, stack, v_, nd_, rh_, 
                            rhR, lh_, temp_, rh_p, lh_p, rhL, temp_p, result_, 
                            v, nd, rh_pu, lhL, lh_pu, temp_pu, rh, lh, lhR, 
                            result, pushedVal >>

O6(self) == /\ pc[self] = "O6"
            /\ lhR' = [lhR EXCEPT ![self] = Mem[lh[self]].R]
            /\ pc' = [pc EXCEPT ![self] = "O7"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, 
                            rhL, temp_p, result_, v, nd, rh_pu, lhL, lh_pu, 
                            temp_pu, rh, lh, temp, result, pushedVal >>

O7(self) == /\ pc[self] = "O7"
            /\ IF /\ LeftHat = lh[self]
                  /\ (Mem[lh[self]].R) = lhR[self]
                  THEN /\ /\ LeftHat' = lhR[self]
                          /\ Mem' = [Mem EXCEPT ![lh[self]].R = lh[self]]
                       /\ temp' = [temp EXCEPT ![self] = TRUE]
                  ELSE /\ temp' = [temp EXCEPT ![self] = FALSE]
                       /\ UNCHANGED << Mem, LeftHat >>
            /\ IF temp'[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "O8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "O1"]
            /\ UNCHANGED << freeList, RightHat, rVal, valBag, stack, v_, nd_, 
                            rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, temp_p, 
                            result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, rh, lh, 
                            lhR, result, pushedVal >>

O8(self) == /\ pc[self] = "O8"
            /\ result' = [result EXCEPT ![self] = Mem[lh[self]].V]
            /\ pc' = [pc EXCEPT ![self] = "O9"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                            stack, v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, 
                            rhL, temp_p, result_, v, nd, rh_pu, lhL, lh_pu, 
                            temp_pu, rh, lh, lhR, temp, pushedVal >>

O9(self) == /\ pc[self] = "O9"
            /\ Mem' = [Mem EXCEPT ![lh[self]].L = Dummy,
                                  ![lh[self]].V = null]
            /\ rVal' = [rVal EXCEPT ![self] = result[self]]
            /\ pc' = [pc EXCEPT ![self] = "O10a"]
            /\ UNCHANGED << freeList, LeftHat, RightHat, valBag, stack, v_, 
                            nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, temp_p, 
                            result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, rh, lh, 
                            lhR, temp, result, pushedVal >>

O10a(self) == /\ pc[self] = "O10a"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ rh' = [rh EXCEPT ![self] = Head(stack[self]).rh]
              /\ lh' = [lh EXCEPT ![self] = Head(stack[self]).lh]
              /\ lhR' = [lhR EXCEPT ![self] = Head(stack[self]).lhR]
              /\ temp' = [temp EXCEPT ![self] = Head(stack[self]).temp]
              /\ result' = [result EXCEPT ![self] = Head(stack[self]).result]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                              v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                              temp_p, result_, v, nd, rh_pu, lhL, lh_pu, 
                              temp_pu, pushedVal >>

O5(self) == /\ pc[self] = "O5"
            /\ rVal' = [rVal EXCEPT ![self] = Mem[lh[self]].V]
            /\ pc' = [pc EXCEPT ![self] = "O5a"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag, stack, 
                            v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                            temp_p, result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, 
                            rh, lh, lhR, temp, result, pushedVal >>

O5a(self) == /\ pc[self] = "O5a"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ rh' = [rh EXCEPT ![self] = Head(stack[self]).rh]
             /\ lh' = [lh EXCEPT ![self] = Head(stack[self]).lh]
             /\ lhR' = [lhR EXCEPT ![self] = Head(stack[self]).lhR]
             /\ temp' = [temp EXCEPT ![self] = Head(stack[self]).temp]
             /\ result' = [result EXCEPT ![self] = Head(stack[self]).result]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, 
                             v_, nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, 
                             temp_p, result_, v, nd, rh_pu, lhL, lh_pu, 
                             temp_pu, pushedVal >>

popLeft(self) == O1(self) \/ O2(self) \/ O3(self) \/ O3a(self) \/ O4(self)
                    \/ O6(self) \/ O7(self) \/ O8(self) \/ O9(self)
                    \/ O10a(self) \/ O5(self) \/ O5a(self)

T1(self) == /\ pc[self] = "T1"
            /\ \/ /\ \E x \in Val:
                       pushedVal' = [pushedVal EXCEPT ![self] = x]
                  /\ valBag' = [valBag EXCEPT ![pushedVal'[self]] = valBag[pushedVal'[self]] + 1]
                  /\ \/ /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pushLeft",
                                                                    pc        |->  "T2",
                                                                    nd        |->  nd[self],
                                                                    rh_pu     |->  rh_pu[self],
                                                                    lhL       |->  lhL[self],
                                                                    lh_pu     |->  lh_pu[self],
                                                                    temp_pu   |->  temp_pu[self],
                                                                    v         |->  v[self] ] >>
                                                                \o stack[self]]
                           /\ v' = [v EXCEPT ![self] = pushedVal'[self]]
                        /\ nd' = [nd EXCEPT ![self] = null]
                        /\ rh_pu' = [rh_pu EXCEPT ![self] = Dummy]
                        /\ lhL' = [lhL EXCEPT ![self] = Dummy]
                        /\ lh_pu' = [lh_pu EXCEPT ![self] = Dummy]
                        /\ temp_pu' = [temp_pu EXCEPT ![self] = Dummy]
                        /\ pc' = [pc EXCEPT ![self] = "N1"]
                        /\ UNCHANGED <<v_, nd_, rh_, rhR, lh_, temp_>>
                     \/ /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pushRight",
                                                                    pc        |->  "T2",
                                                                    nd_       |->  nd_[self],
                                                                    rh_       |->  rh_[self],
                                                                    rhR       |->  rhR[self],
                                                                    lh_       |->  lh_[self],
                                                                    temp_     |->  temp_[self],
                                                                    v_        |->  v_[self] ] >>
                                                                \o stack[self]]
                           /\ v_' = [v_ EXCEPT ![self] = pushedVal'[self]]
                        /\ nd_' = [nd_ EXCEPT ![self] = null]
                        /\ rh_' = [rh_ EXCEPT ![self] = Dummy]
                        /\ rhR' = [rhR EXCEPT ![self] = Dummy]
                        /\ lh_' = [lh_ EXCEPT ![self] = Dummy]
                        /\ temp_' = [temp_ EXCEPT ![self] = Dummy]
                        /\ pc' = [pc EXCEPT ![self] = "L1"]
                        /\ UNCHANGED <<v, nd, rh_pu, lhL, lh_pu, temp_pu>>
                  /\ UNCHANGED <<rh_p, lh_p, rhL, temp_p, result_, rh, lh, lhR, temp, result>>
               \/ /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "popLeft",
                                                                 pc        |->  "T3",
                                                                 rh        |->  rh[self],
                                                                 lh        |->  lh[self],
                                                                 lhR       |->  lhR[self],
                                                                 temp      |->  temp[self],
                                                                 result    |->  result[self] ] >>
                                                             \o stack[self]]
                        /\ rh' = [rh EXCEPT ![self] = Dummy]
                        /\ lh' = [lh EXCEPT ![self] = Dummy]
                        /\ lhR' = [lhR EXCEPT ![self] = Dummy]
                        /\ temp' = [temp EXCEPT ![self] = Dummy]
                        /\ result' = [result EXCEPT ![self] = null]
                        /\ pc' = [pc EXCEPT ![self] = "O1"]
                        /\ UNCHANGED <<rh_p, lh_p, rhL, temp_p, result_>>
                     \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "popRight",
                                                                 pc        |->  "T3",
                                                                 rh_p      |->  rh_p[self],
                                                                 lh_p      |->  lh_p[self],
                                                                 rhL       |->  rhL[self],
                                                                 temp_p    |->  temp_p[self],
                                                                 result_   |->  result_[self] ] >>
                                                             \o stack[self]]
                        /\ rh_p' = [rh_p EXCEPT ![self] = Dummy]
                        /\ lh_p' = [lh_p EXCEPT ![self] = Dummy]
                        /\ rhL' = [rhL EXCEPT ![self] = Dummy]
                        /\ temp_p' = [temp_p EXCEPT ![self] = Dummy]
                        /\ result_' = [result_ EXCEPT ![self] = null]
                        /\ pc' = [pc EXCEPT ![self] = "M1"]
                        /\ UNCHANGED <<rh, lh, lhR, temp, result>>
                  /\ UNCHANGED <<valBag, v_, nd_, rh_, rhR, lh_, temp_, v, nd, rh_pu, lhL, lh_pu, temp_pu, pushedVal>>
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal >>

T2(self) == /\ pc[self] = "T2"
            /\ IF rVal[self] = "full"
                  THEN /\ valBag' = [valBag EXCEPT ![pushedVal[self]] = valBag[pushedVal[self]] - 1]
                  ELSE /\ TRUE
                       /\ UNCHANGED valBag
            /\ pc' = [pc EXCEPT ![self] = "T1"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, stack, v_, 
                            nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, temp_p, 
                            result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, rh, lh, 
                            lhR, temp, result, pushedVal >>

T3(self) == /\ pc[self] = "T3"
            /\ IF rVal[self] # "empty"
                  THEN /\ Assert(valBag[rVal[self]] > 0, 
                                 "Failure of assertion at line 238, column 11.")
                       /\ valBag' = [valBag EXCEPT ![rVal[self]] = valBag[rVal[self]] - 1]
                  ELSE /\ TRUE
                       /\ UNCHANGED valBag
            /\ pc' = [pc EXCEPT ![self] = "T1"]
            /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, stack, v_, 
                            nd_, rh_, rhR, lh_, temp_, rh_p, lh_p, rhL, temp_p, 
                            result_, v, nd, rh_pu, lhL, lh_pu, temp_pu, rh, lh, 
                            lhR, temp, result, pushedVal >>

test(self) == T1(self) \/ T2(self) \/ T3(self)

Next == (\E self \in ProcSet:  \/ pushRight(self) \/ popRight(self)
                               \/ pushLeft(self) \/ popLeft(self))
           \/ (\E self \in Procs: test(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

Symmetry == Permutations(Address \ {Dummy}) \cup Permutations(Procs)

Liveness == \A p \in Procs : []<> (pc[p] = "T1")
=============================================================================

Checked on SVC-LAMPORT-3 with
   CONSTANTS Val = {v1, v2}
             Address = {a1, a2, a3}
             Dummy = a1
             Procs = {p1, p2}
             null = null
             GC = GC

found 2886585 states, depth 67, in 17 min 38.3 sec

==============================

Run on SVC-LAMPORT-2 with

   CONSTANTS Val = {v1}
             Address = {a1, a2, a3, a4}
             Dummy = a1
             Procs = {p1, p2, p3}
             null = null
             GC = GC

stopped after 1482 min 40 sec, with
109078490 states generated, 37886049 distinct states, 5107502 states
left on queue.
