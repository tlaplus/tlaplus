last modified on Thu  2 Feb 2006 at 15:40:27 PST by lamport

The translator was renaming i to i_ in procedure IsAlgorithm, but
it failed to rename the i in the while test of statement IA3.

--------------------------- MODULE bug_05_12_10a ---------------------------
EXTENDS Naturals, Sequences, FiniteSets , TLC
IsSeq(x)         == DOMAIN x = 1..Len(x)
IsNonemptySeq(x) == IsSeq(x) /\ (Len(x) > 0)

alg == [type |-> "uniprocess",
        name  |-> "Quicksort", 
        decls  |-> << >>,
        defs   |-> <<  >>,
        prcds  |-> << >>,
        body  |-> <<1>>]

(* 
--algorithm Pcal
  procedure IsAlgorithm(A)
    variable res = FALSE ; i = 0 ;
    begin IA1: assert \/ /\ A.type = "uniprocess"
                         /\ DOMAIN A = {"type", "name", "defs", 
                                           "decls", "prcds", "body"}
                      \/ /\ A.type = "multiiprocess"
                         /\ DOMAIN A = {"type", "name", "defs", 
                                            "decls", "prcds", "procs"};
               assert A.name \in STRING ;
               call IsExpr(A.defs) ;
          IA2: assert IsSeq(A.decls) ;
               i := Len(A.decls) ;
          IA3: while i > 0 do call IsVarDecl(A.decls[i]) ;
                        IA3a: i := i-1 
               end while ;
               i := Len(A.prcds) ;
          IA4: while i > 0 do call IsProcedure(A.prcds[i]) ;
                        IA4a: i := i-1 
               end while ;
               if A.type = "uniprocess"
                 then assert IsNonemptySeq(A.body) ;
                             i := Len(A.body) ;
                 IA5: while i > 0 do call IsLabeledStmt(A.body[i])  ;
                               IA5a: i := i-1 
                      end while ;
                 else assert IsNonemptySeq(A.procs) ;
                             i := Len(A.procs) ;
                 IA6: while i > 0 do call IsProcess(A.procs[i])  ;
                               IA6a: i := i-1 
                      end while ;
               end if ;
          IA7: return ;
    end procedure
  procedure IsExpr(exp)
    variable i ;
    begin IE1 : assert IsSeq(exp) ;
               i := Len(exp) ;
          IE2: while i > 0 do assert exp[i] \in STRING  ;
                        IA5a: i := i-1 
               end while ;
               return               
    end procedure
  procedure IsVarDecl(vdcl)
    begin IV1 : return 
    end procedure
  procedure IsProcedure(prcdr)
    begin IP1 : return 
    end procedure
  procedure IsLabeledStmt(lstmt)
    begin IL1 : return 
    end procedure
  procedure IsProcess(proc)
    begin IPr1 : return 
    end procedure
  begin PC1: call IsAlgorithm(alg) ;
        Pc2: print "IsAlgorithm(alg) = TRUE"
  end algorithm
*)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-019f5cd9d60f4235bafaf7162f8ed3b4
\* Label IA5a of procedure IsAlgorithm at line 43 col 38 changed to IA5a_
\* Procedure variable i of procedure IsAlgorithm at line 21 col 28 changed to i_
CONSTANT defaultInitValue
VARIABLES pc, stack, A, res, i_, exp, i, vdcl, prcdr, lstmt, proc

vars == << pc, stack, A, res, i_, exp, i, vdcl, prcdr, lstmt, proc >>

Init == (* Procedure IsAlgorithm *)
        /\ A = defaultInitValue
        /\ res = FALSE
        /\ i_ = 0
        (* Procedure IsExpr *)
        /\ exp = defaultInitValue
        /\ i = defaultInitValue
        (* Procedure IsVarDecl *)
        /\ vdcl = defaultInitValue
        (* Procedure IsProcedure *)
        /\ prcdr = defaultInitValue
        (* Procedure IsLabeledStmt *)
        /\ lstmt = defaultInitValue
        (* Procedure IsProcess *)
        /\ proc = defaultInitValue
        /\ stack = << >>
        /\ pc = "PC1"

IA1 == /\ pc = "IA1"
       /\ Assert(\/ /\ A.type = "uniprocess"
                    /\ DOMAIN A = {"type", "name", "defs",
                                      "decls", "prcds", "body"}
                 \/ /\ A.type = "multiiprocess"
                    /\ DOMAIN A = {"type", "name", "defs",
                                       "decls", "prcds", "procs"}, 
                 "Failure of assertion at line 22, column 16.")
       /\ Assert(A.name \in STRING, 
                 "Failure of assertion at line 28, column 16.")
       /\ /\ exp' = A.defs
          /\ stack' = << [ procedure |->  "IsExpr",
                           pc        |->  "IA2",
                           i         |->  i,
                           exp       |->  exp ] >>
                       \o stack
       /\ i' = defaultInitValue
       /\ pc' = "IE1"
       /\ UNCHANGED << A, res, i_, vdcl, prcdr, lstmt, proc >>

IA2 == /\ pc = "IA2"
       /\ Assert(IsSeq(A.decls), 
                 "Failure of assertion at line 30, column 16.")
       /\ i_' = Len(A.decls)
       /\ pc' = "IA3"
       /\ UNCHANGED << stack, A, res, exp, i, vdcl, prcdr, lstmt, proc >>

IA3 == /\ pc = "IA3"
       /\ IF i_ > 0
             THEN /\ /\ stack' = << [ procedure |->  "IsVarDecl",
                                      pc        |->  "IA3a",
                                      vdcl      |->  vdcl ] >>
                                  \o stack
                     /\ vdcl' = A.decls[i_]
                  /\ pc' = "IV1"
                  /\ i_' = i_
             ELSE /\ i_' = Len(A.prcds)
                  /\ pc' = "IA4"
                  /\ UNCHANGED << stack, vdcl >>
       /\ UNCHANGED << A, res, exp, i, prcdr, lstmt, proc >>

IA3a == /\ pc = "IA3a"
        /\ i_' = i_-1
        /\ pc' = "IA3"
        /\ UNCHANGED << stack, A, res, exp, i, vdcl, prcdr, lstmt, proc >>

IA4 == /\ pc = "IA4"
       /\ IF i_ > 0
             THEN /\ /\ prcdr' = A.prcds[i_]
                     /\ stack' = << [ procedure |->  "IsProcedure",
                                      pc        |->  "IA4a",
                                      prcdr     |->  prcdr ] >>
                                  \o stack
                  /\ pc' = "IP1"
                  /\ i_' = i_
             ELSE /\ IF A.type = "uniprocess"
                        THEN /\ Assert(IsNonemptySeq(A.body), 
                                       "Failure of assertion at line 40, column 23.")
                             /\ i_' = Len(A.body)
                             /\ pc' = "IA5"
                        ELSE /\ Assert(IsNonemptySeq(A.procs), 
                                       "Failure of assertion at line 45, column 23.")
                             /\ i_' = Len(A.procs)
                             /\ pc' = "IA6"
                  /\ UNCHANGED << stack, prcdr >>
       /\ UNCHANGED << A, res, exp, i, vdcl, lstmt, proc >>

IA4a == /\ pc = "IA4a"
        /\ i_' = i_-1
        /\ pc' = "IA4"
        /\ UNCHANGED << stack, A, res, exp, i, vdcl, prcdr, lstmt, proc >>

IA5 == /\ pc = "IA5"
       /\ IF i_ > 0
             THEN /\ /\ lstmt' = A.body[i_]
                     /\ stack' = << [ procedure |->  "IsLabeledStmt",
                                      pc        |->  "IA5a_",
                                      lstmt     |->  lstmt ] >>
                                  \o stack
                  /\ pc' = "IL1"
             ELSE /\ pc' = "IA7"
                  /\ UNCHANGED << stack, lstmt >>
       /\ UNCHANGED << A, res, i_, exp, i, vdcl, prcdr, proc >>

IA5a_ == /\ pc = "IA5a_"
         /\ i_' = i_-1
         /\ pc' = "IA5"
         /\ UNCHANGED << stack, A, res, exp, i, vdcl, prcdr, lstmt, proc >>

IA6 == /\ pc = "IA6"
       /\ IF i_ > 0
             THEN /\ /\ proc' = A.procs[i_]
                     /\ stack' = << [ procedure |->  "IsProcess",
                                      pc        |->  "IA6a",
                                      proc      |->  proc ] >>
                                  \o stack
                  /\ pc' = "IPr1"
             ELSE /\ pc' = "IA7"
                  /\ UNCHANGED << stack, proc >>
       /\ UNCHANGED << A, res, i_, exp, i, vdcl, prcdr, lstmt >>

IA6a == /\ pc = "IA6a"
        /\ i_' = i_-1
        /\ pc' = "IA6"
        /\ UNCHANGED << stack, A, res, exp, i, vdcl, prcdr, lstmt, proc >>

IA7 == /\ pc = "IA7"
       /\ pc' = Head(stack).pc
       /\ res' = Head(stack).res
       /\ i_' = Head(stack).i_
       /\ A' = Head(stack).A
       /\ stack' = Tail(stack)
       /\ UNCHANGED << exp, i, vdcl, prcdr, lstmt, proc >>

IsAlgorithm == IA1 \/ IA2 \/ IA3 \/ IA3a \/ IA4 \/ IA4a \/ IA5 \/ IA5a_
                  \/ IA6 \/ IA6a \/ IA7

IE1 == /\ pc = "IE1"
       /\ Assert(IsSeq(exp), "Failure of assertion at line 55, column 17.")
       /\ i' = Len(exp)
       /\ pc' = "IE2"
       /\ UNCHANGED << stack, A, res, i_, exp, vdcl, prcdr, lstmt, proc >>

IE2 == /\ pc = "IE2"
       /\ IF i > 0
             THEN /\ Assert(exp[i] \in STRING, 
                            "Failure of assertion at line 57, column 31.")
                  /\ pc' = "IA5a"
                  /\ UNCHANGED << stack, exp, i >>
             ELSE /\ pc' = Head(stack).pc
                  /\ i' = Head(stack).i
                  /\ exp' = Head(stack).exp
                  /\ stack' = Tail(stack)
       /\ UNCHANGED << A, res, i_, vdcl, prcdr, lstmt, proc >>

IA5a == /\ pc = "IA5a"
        /\ i' = i-1
        /\ pc' = "IE2"
        /\ UNCHANGED << stack, A, res, i_, exp, vdcl, prcdr, lstmt, proc >>

IsExpr == IE1 \/ IE2 \/ IA5a

IV1 == /\ pc = "IV1"
       /\ pc' = Head(stack).pc
       /\ vdcl' = Head(stack).vdcl
       /\ stack' = Tail(stack)
       /\ UNCHANGED << A, res, i_, exp, i, prcdr, lstmt, proc >>

IsVarDecl == IV1

IP1 == /\ pc = "IP1"
       /\ pc' = Head(stack).pc
       /\ prcdr' = Head(stack).prcdr
       /\ stack' = Tail(stack)
       /\ UNCHANGED << A, res, i_, exp, i, vdcl, lstmt, proc >>

IsProcedure == IP1

IL1 == /\ pc = "IL1"
       /\ pc' = Head(stack).pc
       /\ lstmt' = Head(stack).lstmt
       /\ stack' = Tail(stack)
       /\ UNCHANGED << A, res, i_, exp, i, vdcl, prcdr, proc >>

IsLabeledStmt == IL1

IPr1 == /\ pc = "IPr1"
        /\ pc' = Head(stack).pc
        /\ proc' = Head(stack).proc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << A, res, i_, exp, i, vdcl, prcdr, lstmt >>

IsProcess == IPr1

PC1 == /\ pc = "PC1"
       /\ /\ A' = alg
          /\ stack' = << [ procedure |->  "IsAlgorithm",
                           pc        |->  "Pc2",
                           res       |->  res,
                           i_        |->  i_,
                           A         |->  A ] >>
                       \o stack
       /\ res' = FALSE
       /\ i_' = 0
       /\ pc' = "IA1"
       /\ UNCHANGED << exp, i, vdcl, prcdr, lstmt, proc >>

Pc2 == /\ pc = "Pc2"
       /\ PrintT("IsAlgorithm(alg) = TRUE")
       /\ pc' = "Done"
       /\ UNCHANGED << stack, A, res, i_, exp, i, vdcl, prcdr, lstmt, proc >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == IsAlgorithm \/ IsExpr \/ IsVarDecl \/ IsProcedure \/ IsLabeledStmt
           \/ IsProcess \/ PC1 \/ Pc2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-1e7f8dbaa6644662e3fa38b76045e01d
=============================================================================
